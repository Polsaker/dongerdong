#!/usr/bin/env python3
# -*- coding: utf-8
import logging
import json
import re
import html
import traceback
import time
import random
import copy
import datetime
import threading
import importlib
import subprocess
import peewee
from pyfiglet import Figlet
from matrix_client.client import MatrixClient

loggingFormat = '%(asctime)s %(levelname)s:%(name)s: %(message)s'
#logging.basicConfig(level=logging.DEBUG, format=loggingFormat)

config = json.load(open("config.json"))
IRC_COLOR_MAP = {'0': '#FFFFFF', '00': '#FFFFFF', '1': '#000000', '01': '#000000', '2': '#00007F', '02': '#00007F', '3': '#009300', '03': '#009300', '4': '#FF0000', '04': '#FF0000', '5': '#7F0000', '05': '#7F0000', '6': '#9C009C', '06': '#9C009C', '7': '#FC7F00', '07': '#FC7F00', '8': '#FFFF00', '08': '#FFFF00', '9': '#00FC00', '09': '#00FC00', '10': '#009393', '11': '#00FFFF', '12': '#0000FC', '13': '#FF00FF', '14': '#7F7F7F', '15': '#D2D2D2'}


class Message(object):
    def __init__(self, roomchunk):
        self.source = roomchunk['sender']
        self.target = roomchunk['room_id']
        self.message = roomchunk['content'].get('body')
        
        self.is_command = True if self.message.strip()[0] == '!' else False
        if self.is_command:
            self.command = self.message.strip()[1:].split(' ')[0].lower()
        self.args = self.message.rstrip().split(" ")[1:]
        self.text = " ".join(self.args)
        
        self.event_id = roomchunk['event_id']

    def __repr__(self):
        return "<Message from:{0} to:{1} - {2} (command: {3})>".format(self.source, self.target, self.message, self.command if self.is_command else "no")


class DongerDong(object):
    def __init__(self):
        self.client = None
        self.logger = logging.Logger('dongerdong')

        self.channel = config['channel']  # Main fight channel

        self.pendingFights = {}  # Pending (not !accepted) fights. ({'player': {'ts': 123, 'deathmatch': False, 'versusone': False, 'players': [...], 'pendingaccept': [...]}, ...}

        # Game vars (Reset these in self.win)
        self.deathmatch = False
        self.gameRunning = False
        self.turnStart = 0
        self.players = {}  # Players. {'polsaker': {'hp': 100, 'heals': 5, 'zombie': False, 'praised': False, 'gdr': 1}, ...}
        self.gdrmodifier = 1  # Modifier for damage reduction adjustment, increase for higher defense, decrease for lower defense
        self.turnlist = []  # Same as self.players, but only the player nicks. Shuffled when the game starts (used to decide turn orders)
        self.accountlist = []  # list of accounts of every player that joined the current fight
        self.currentTurn = -1  # current turn = turnlist[currentTurn]

        self.lastheardfrom = {}  # lastheardfrom['Polsaker'] = time.time()
        self.sourcehistory = []  # sourcehistory.append(source)
        self.lastbotfight = time.time() - 30  # Last time the bot was in a fight.

        self.poke = False  # True if we poked somebody

        self.currgamerecord = None  # GameStats object for current game

        self.accounts = {}  # Maps (user_id, displayname or user) to user_id
        self.users = {}  # Maps user_id to displayname

        timeout_checker = threading.Thread(target=self._timeout)
        timeout_checker.daemon = True
        timeout_checker.start()
        self.import_extcmds()
    
    def connect(self):
        try:
            tok = json.load(open('.token', 'r'))
            self.client = MatrixClient(config['homeserver'], token=tok['token'], user_id=tok['user_id'])
        except FileNotFoundError:
            self.client = MatrixClient(config['homeserver'])
            token = self.client.login_with_password(username=config['username'], password=config['password'])
            json.dump({'token': token, 'user_id': self.client.user_id}, open('.token', 'w'))
        
        self.default_power_levels = {
                    "kick":99,
                    "notifications":{"room":99},
                    "ban":99,
                    "users":{
                        self.client.user_id: 100
                    },
                    "users_default":0,
                    "redact":99,
                    "events_default":0,
                    "invite":0,
                    "events":{
                        "m.room.canonical_alias":99,
                        "m.room.name":99,
                        "m.room.power_levels":99,
                        "im.vector.modular.widgets":99,
                        "m.room.history_visibility":99,
                        "m.room.topic":99,
                        "m.room.avatar":99
                    },
                    "state_default":99
                    }
        for i in config['admins']:
            self.default_power_levels['users'][i] = 99
        self.client.api.set_power_levels(self.channel, self.default_power_levels)
        self.client.add_invite_listener(self.on_invite)
        self.client.add_listener(self.on_message, 'm.room.message')
        self.client.add_listener(self.on_member, 'm.room.member')
        self.accounts, self.users = self.getRoomMembers(self.channel)
        self.client.listen_forever(exception_handler=lambda x: print(traceback.format_exc()))

    def mute_room(self, users):
        """ users = list of users authorized to speak """
        self.orig_topic = self.client.api.get_room_topic(self.channel)['topic']
        self.client.api.set_room_topic(self.channel, 'DONGERDONG - FIGHT IN PROGRESS: {0}'.format(' vs '.join(users)))
        privdict = copy.deepcopy(self.default_power_levels)
        privdict['events_default'] = 50
        for i in users:
            if not privdict['users'].get(i):
                privdict['users'][i] = 50
        
        self.client.api.set_power_levels(self.channel, privdict)
    
    def restore_room(self):
        self.client.api.set_room_topic(self.channel, self.orig_topic)
        self.client.api.set_power_levels(self.channel, self.default_power_levels)

    def on_member(self, us):
        if us['content']['membership'] != 'join':
            return
        self.accounts[us['sender']] = us['sender']
        self.accounts[us['sender'][1:].split(':')[0]] = us['sender']
        self.accounts[us['content']['displayname']] = us['sender']
        self.accounts[us['content']['displayname'].lower()] = us['sender']
        self.users[us['sender']] = us['content']['displayname']
        

    def on_invite(self, room_id, state):
        self.client.join_room(room_id)
        self.logger.info('Got an invite for {0}. Joining.'.format(room_id))

    def on_message(self, data):
        if data['content']['msgtype'] == 'm.notice':
            return
        
        ev = Message(data)
        print('> {0}'.format(ev))

        if ev.is_command:
            if ev.target == self.channel:
                if ev.command in ('fight', 'duel', 'deathmatch') and not self.gameRunning:
                    if not ev.args:
                        self.html_message(ev.target, 'Can you even <b>READ</b>?! It is !{0} <nick>{1}'.format(ev.command, " [othernick] [...] " if ev.command == "fight" else ""))
                        return
                    
                    if ev.source in ev.args:
                        return self.html_message(ev.target, "Don't fight yourself, dummy.")
                    
                    if ev.command == 'deathmatch':
                        return self.message(ev.target, 'Deathmatches not implemented yet')

                    if ev.command == "deathmatch" and len(ev.args) > 1:
                        return self.html_message(ev.target, "Deathmatches are 1v1 only.")
                    
                    if ev.command == "duel" and len(ev.args) > 1:
                        return self.html_message(ev.target, "Challenges are 1v1 only.")
                    
                    self.fight(players=[ev.source] + ev.args,
                            deathmatch=True if ev.command == "deathmatch" else False,
                            versusone=True if (ev.command == "deathmatch" or ev.command == "duel") else False)
                elif ev.command == "accept" and not self.gameRunning:
                    if not ev.args:
                        self.message(ev.target, "Can you read? It is !accept <nick>")
                        return

                    challenger = self.accounts.get(ev.args[0].lower(), ev.args[0].lower())
                    opportunist = False

                    # Check if the user was challenged
                    try:
                        if ev.source.lower() not in self.pendingFights[challenger]['pendingaccept']:
                            if "*" in self.pendingFights[challenger]['pendingaccept']:
                                if ev.source.lower() == challenger:
                                    self.message(ev.target, "You're trying to fight yourself?")
                                    return

                                opportunist = True
                            else:
                                self.message(ev.target, "Err... Maybe you meant to say \002!fight {0}\002? They never challenged you.".format(ev.args[0]))
                                return
                    except KeyError:  # self.pendingFights[x] doesn't exist
                        self.message(ev.target, "Err... Maybe you meant to say \002!fight {0}\002? They never challenged you.".format(ev.args[0]))
                        return

                    # Check if the challenger is here
                    if ev.args[0].lower() not in map(str.lower, self.accounts):
                        self.message(ev.target, "They're not here anymore - maybe they were intimidated by your donger.")
                        del self.pendingFights[challenger]  # remove fight.
                        return

                    # OK! This player accepted the fight.
                    self.pendingFights[challenger]['players'].append(ev.source)
                    if not opportunist:
                        self.pendingFights[challenger]['pendingaccept'].remove(ev.source.lower())
                    else:
                        self.pendingFights[challenger]['pendingaccept'].remove('*')

                    # Check if everybody accepted
                    if not self.pendingFights[challenger]['pendingaccept']:
                        # Start the game!
                        self.start(self.pendingFights[challenger])

                elif ev.command == "hit" and self.gameRunning:
                    if ev.source != self.turnlist[self.currentTurn]:
                        self.message(self.channel, "It's not your fucking turn!")
                        return

                    if not ev.args:  # pick a random living thing
                        livingThings = [self.players[player]['nick'] for player in self.players if self.players[player]['hp'] > 0 and player != ev.source.lower()]
                        self.hit(ev.source, random.choice(livingThings))
                    else:  # The user picked a thing. Check if it is alive
                        if self.accounts.get(ev.args[0].lower()) not in self.players:
                            self.message(self.channel, "You should hit something that is actually playing...")
                            return
                        if self.accounts.get(ev.args[0].lower()) == ev.source.lower():
                            self.message(self.channel, "Stop hitting yourself!")
                            return
                        if self.players[self.accounts.get(ev.args[0].lower())]['hp'] <= 0:
                            self.message(self.channel, "Do you REALLY want to hit a corpse?")
                            return

                        self.hit(ev.source, self.players[self.accounts.get(ev.args[0].lower())]['nick'])
                elif ev.command == "heal" and self.gameRunning:
                    if ev.source != self.turnlist[self.currentTurn]:
                        self.message(self.channel, "It's not your fucking turn!")
                        return

                    self.heal(ev.source)
                elif ev.command == "praise" and self.gameRunning:
                    if ev.source != self.turnlist[self.currentTurn]:
                        self.message(self.channel, "It's not your fucking turn!")
                        return

                    if self.deathmatch:
                        self.message(ev.target, "You can't praise during deathmatches. It's still your turn.")
                        return

                    if self.players[ev.source.lower()]['praised']:
                        self.message(ev.target, "You can only praise once per game. It's still your turn.")
                        return

                    if not ev.args:
                        ptarget = ev.source
                    else:
                        try:
                            ptarget = self.players[self.accounts.get(ev.args[0].lower(), ev.args[0])]['nick']
                        except KeyError:
                            self.message(ev.target, "Player not found.")
                            return
                    praiseroll = random.randint(1, 3)
                    self.players[ev.source.lower()]['praised'] = True
                    if self.deathmatch or self.versusone:
                        if ev.source.lower() == self.currgamerecord.player1:
                            self.currgamerecord.player1_praiseroll = praiseroll
                        else:
                            self.currgamerecord.player2_praiseroll = praiseroll

                    if self.client.user_id in self.turnlist:
                        self.message(ev.target, "You DARE try and suckle my donger while fighting me?!")
                        praiseroll = 2
                        ptarget = self.players[ev.source.lower()]['nick']

                    if praiseroll == 1:
                        self.ascii("WHATEVER")
                        self.heal(ptarget, True)  # Critical heal
                    elif praiseroll == 2:
                        self.ascii("FUCK YOU")
                        self.hit(ev.source, ptarget, True)
                    else:
                        self.ascii("NOPE")
                        self.getTurn()
                    self.countStat(ev.source, "praises")
                elif ev.command == "cancel" and not self.gameRunning:
                    try:
                        del self.pendingFights[ev.source.lower()]
                        self.message(ev.target, "Fight cancelled.")
                    except KeyError:
                        self.message(ev.target, "You can only !cancel if you started a fight.")
                        return
                elif ev.command == "reject" and not self.gameRunning:
                    if not ev.args:
                        self.message(ev.target, "Can you read? It's !reject <nick>")
                        return

                    try:  # I could just use a try.. except in the .remove(), but I am too lazy to remove this chunk of code
                        if ev.source.lower() not in self.pendingFights[self.accounts.get(ev.args[0].lower())]['pendingaccept']:
                            self.message(ev.target, "{0} didn't challenge you.".format(ev.args[0]))
                            return
                    except KeyError:  # if self.pendingFights[args[0].lower()] doesn't exist.
                        self.message(ev.target, "{0} didn't challenge you.".format(ev.args[0]))
                        return

                    self.pendingFights[self.accounts.get(ev.args[0].lower())]['pendingaccept'].remove(ev.source.lower())
                    self.message(ev.target, "\002{0}\002 fled the fight".format(ev.source))

                    if not self.pendingFights[self.accounts.get(ev.args[0].lower())]['pendingaccept']:
                        if len(self.pendingFights[self.accounts.get(ev.args[0].lower())]['players']) == 1:  # only the challenger
                            self.message(ev.target, "Fight cancelled.")
                            del self.pendingFights[self.accounts.get(ev.args[0].lower())]
                        else:
                            self.start(self.pendingFights[self.accounts.get(ev.args[0].lower())])
                elif ev.command == "quit" and self.gameRunning:
                    self.cowardQuit(ev.source)
                elif ev.command == "stats" and not self.gameRunning:
                    if ev.args:
                        nick = ev.args[0]
                    else:
                        nick = ev.source
                    try:
                        nick = self.accounts[nick]
                    except KeyError:
                        pass

                    stats = self.getStats(nick)

                    if not stats:
                        return self.message(ev.target, "No stats for \002{0}\002.".format(nick))

                    balance = stats.wins - (stats.losses + stats.idleouts + (stats.quits * 2))

                    balance = ("+" if balance > 0 else "") + str(balance)

                    top = self.top_dongers().dicts()
                    ranking = next((index for (index, d) in enumerate(top) if d['name'].lower() == stats.name.lower()), -1) + 1

                    if ranking == 0:
                        ranking = "\002Not ranked\002."
                    elif ranking == 1:
                        ranking = "Ranked \002\003071st\003\002"
                    elif ranking == 2:
                        ranking = "Ranked \002\003142nd\003\002"
                    elif ranking == 3:
                        ranking = "Ranked \002\003063rd\003\002"
                    else:
                        ranking = "Ranked \002{}th\002".format(ranking)
                    #try:
                    #    d0 = stats.lastplayed.date()
                    #    today = datetime.datetime.now().date()
                    #    delta = today - d0
                    #    aelo = stats.elo - (int(delta.days)*2) #aelo (adjusted ELO) is equal to normal ELO minus (days since last played times two)
                    #except:
                    #    self.message(target, "You activated the special secret 1331589151jvlhjv feature!")

                    self.message(ev.target, "\002{0}\002's stats: \002{1}\002 wins, \002{2}\002 losses, \002{4}\002 coward quits, \002{5}\002 idle-outs (\002{3}\002), "
                                            "\002{6}\002 !praises, \002{7}\002 matches, \002{8}\002 deathmatches (\002{9}\002 total). "
                                            "{11} (\002{10}\002 points)"
                                            .format(stats.name, stats.wins, stats.losses, balance, stats.quits, stats.idleouts, stats.praises,
                                                    stats.matches, stats.deathmatches, (stats.matches + stats.deathmatches), stats.elo, ranking))
                elif ev.command in ("top", "shame") and not self.gameRunning:
                    p = self.top_dongers((ev.command == "shame")).limit(5)  # If command == shame, then we're passing "True" into the top_dongers function below (in the "bottom" argument), overriding the default False
                    if not p:
                        return self.message(ev.target, "No top dongers.")
                    c = 1
                    for player in p:
                        playernick = "{0}\u200b{1}".format(player.name[0], player.name[1:])

                        self.message(ev.target, "{0} - \002{1}\002 (\002{2}\002)".format(c, playernick.upper(), player.elo))
                        c += 1

                    if config.get('stats-url'):
                        self.message(ev.target, "Full stats at {}".format(config['stats-url']))
            # Rate limiting
            try:
                if ev.target != self.channel:  # If the command is happening in a place besides the primary channel...
                    if time.time() - self.lastheardfrom[ev.source] < 7:  # And it's been seven seconds since this person has made a command...
                        if ev.source == self.sourcehistory[-2] and ev.source == self.sourcehistory[-1]:  # And they made the last two commands...
                            if ev.source not in config['admins']:  # And the person is not an administrator...
                                return  # Ignore it
            except KeyError:
                pass
            finally:
                self.lastheardfrom[ev.source] = time.time()
                self.sourcehistory.append(ev.source)

            # Regular commands
            if ev.command == "raise":
                self.message(ev.target, "ヽ༼ຈل͜ຈ༽ﾉ RAISE YOUR DONGERS ヽ༼ຈل͜ຈ༽ﾉ")
            elif ev.command == "lower":
                self.message(ev.target, "┌༼ຈل͜ຈ༽┐ ʟᴏᴡᴇʀ ʏᴏᴜʀ ᴅᴏɴɢᴇʀs ┌༼ຈل͜ຈ༽┐")
            elif ev.command == "help":
                exhelp = ""
                for ch in self.cmdhelp.keys():
                    if self.cmds[ch].adminonly and ev.source not in config['admins']:
                        continue
                    exhelp += "<li>!{}: {}</li>".format(ch, self.cmdhelp[ch])
                self.html_message(ev.target, "Commands available only in <a href=\"https://matrix.to/#/{0}\">{0}</a>:".format(self.channel) +
                            "<ul><li>!fight <nickname> [othernicknames]: Challenge another player, or multiple players.</li>" +
                            "<li>!duel <nickname>: Same as fight, but only 1v1.</li>" +
                            "<li>!deathmatch <nickname>: Same as duel, but the loser is bant for 20 minutes.</li>" +
                            "<li>!ascii <text>: Turns any text 15 characters or less into ascii art</li>" +
                            "<li>!cancel: Cancels a !fight</li>" +
                            "<li>!reject <nick>: Rejects a !fight</li>" +
                            "<li>!stats [player]: Outputs player's game stats (or your own stats)</li>" +
                            "<li>!top, !shame: Lists the best, or the worst, players</li></ul>" +
                            "Commands available everywhere: <ul>{0}</ul>".format(exhelp))
            elif ev.command == "version":
                try:
                    ver = subprocess.check_output(["git", "describe", "--tags"]).decode().strip()
                    self.message(ev.target, "I am running {} ({})".format(ver, 'http://bit.ly/1pG2Hay'))
                except:
                    self.message(ev.target, "I have no idea.")
            elif ev.command in self.extcmds:  # Extended commands support
                try:
                    if self.cmds[ev.command].adminonly and ev.source not in config['admins']:
                        return
                except AttributeError:
                    pass
                self.cmds[ev.command].doit(self, ev.target, ev.source)


    def cowardQuit(self, coward):
        # check if it's playing
        if coward not in self.turnlist:
            return
        if self.players[coward.lower()]['hp'] <= 0:  # check if it is alive
            return

        self.ascii("COWARD")
        self.message(self.channel, "The coward is dead!")

        self.players[coward.lower()]['hp'] = -1

        self.kick(self.channel, coward, "COWARD")
        self.countStat(coward, "quits")

        if self.deathmatch:
            self.akick(coward)

        if self.turnlist[self.currentTurn].lower() == coward.lower():
            self.getTurn()
        else:
            aliveplayers = 0
            # TODO: Do this in a neater way
            for p in self.players:
                if self.players[p]['hp'] > 0:
                    aliveplayers += 1
                    survivor = p

            if aliveplayers == 1:
                self.win(survivor, False)


    def fight(self, players, deathmatch=False, versusone=False):
        # Check if those users are in the channel, if they're identified, etc
        accounts = []
        
        openSpots = 0

        for player in players[:]:
            if player == "*":
                openSpots += 1
                continue

            if player.lower() not in map(str.lower, self.accounts):
                self.message(self.channel, "\002{0}\002 is not in the channel.".format(player))
                return

            if self.accounts[player] in accounts:
                players.remove(player)
                continue

            accounts.append(self.accounts[player])

        if len(accounts) <= 1:
            self.message(self.channel, "You need more than one person to fight!")
            return

        self.pendingFights[accounts[0].lower()] = {
            'ts': time.time(),  # Used to calculate the expiry time for a fight
            'deathmatch': deathmatch,
            'versusone': versusone,
            'pendingaccept': [x.lower() for x in accounts[1:]],
            'players': [accounts[0]], # we initially add only the player that started the fight
        }
        if self.client.user_id in accounts:  # If a user is requesting the bot participate in a fight...
            if versusone:  # If it's a duel or deathmatch, refuse
                return self.message(self.channel, "{0} is not available for duels or deathmatches".format(config['username']))
            if (time.time() - self.lastbotfight < 30):  # Prevent the bot from fighting with someone within 30 seconds of its last fight with someone. Trying to stop people from taking over the channel
                return self.message(self.channel, "{0} needs a 30 second break before participating in a fight.".format(config['username']))
            self.message(self.channel, "YOU WILL SEE")
            self.pendingFights[accounts[0].lower()]['pendingaccept'].remove(self.client.user_id.lower())
            self.pendingFights[accounts[0].lower()]['players'].append(self.client.user_id)
            if not self.pendingFights[accounts[0].lower()]['pendingaccept']:
                # Start the game!
                self.start(self.pendingFights[accounts[0].lower()])
                return
            accounts.remove(self.client.user_id)

        accounts[:] = [x for x in accounts if x != '*']  # This magically makes it so you can issue a wildcard challenge to anyone. No one knows how this works but we stopped asking questions long ago.

        if len(accounts) > 1:
            if deathmatch:
                self.message(self.channel, "{0}: \002{1}\002 challenged you to a deathmatch. The loser will be bant for 20 minutes. To accept, use '!accept {1}'.".format(", ".join(players[1:]), players[0]), message_type='m.text')
            else:
                self.message(self.channel, "{0}: \002{1}\002 challenged you. To accept, use '!accept {1}'.".format(", ".join(accounts[1:]), accounts[0]), message_type='m.text')
        else:
            self.message(self.channel, "\002{0}\002 has challenged anybody willing to fight{1}. To accept, use '!accept {0}'.".format(accounts[0], " to the death. The loser will be bant for 20 minutes" if deathmatch else ""), message_type='m.text')

        if openSpots == 1 and len(accounts) > 1:
            self.message(self.channel, "This fight has an open spot for anybody to join.")
        elif openSpots > 1:
            self.message(self.channel, "This fight has open spots for {0} players to join.".format(openSpots))


    def start(self, pendingFight):
        self.gameRunning = True
        self.pendingFights = {}
        self.deathmatch = pendingFight['deathmatch']
        self.versusone = pendingFight['versusone']

        if self.deathmatch or self.versusone:
            self.currgamerecord = GameStats.create(player1=pendingFight['players'][0],
                                                   player2=pendingFight['players'][1])

        if self.deathmatch:
            self.ascii("DEATHMATCH", font="fire_font-s", lineformat="\00304")

        if len(pendingFight['players']) == 2:
            self.ascii(" VS ".join(pendingFight['players']).upper(), "straight")

        self.html_message(self.channel, "RULES:<br><ol><li>Wait your turn. One person at a time.</li><li>Be a dick about it.</li></ol><br>Use !hit [nick] to strike.<br>Use !heal to heal yourself.")
        # TODO: join mid-fight
        #if not self.versusone:  # Users can't join a fight if it's versusone (duel or deathmatch)
        #    self.message(self.channel, "Use '/msg {0} !join' to join a game mid-fight.".format(self.client.user_id))
        if not self.deathmatch:  # Users can't praise if it's a deathmatch
            if self.client.user_id not in pendingFight['players'] or len(pendingFight['players']) > 2:
                self.message(self.channel, "Use !praise [nick] to praise the donger gods (once per game).")

        self.message(self.channel, " ")

        # Set up the fight
        for player in pendingFight['players']:
            # TODO: Stats
            if self.deathmatch:
                self.countStat(player, "deathmatches")
            elif self.versusone:
                self.countStat(player, "matches")
            self.accountlist.append(player)
            self.players[player.lower()] = {'hp': 100, 'heals': 5, 'zombie': False, 'nick': player, 'praised': False, 'gdr': 1}
            self.turnlist.append(player)

        random.shuffle(self.turnlist)
        self.ascii("FIGHT")

        self.mute_room(self.turnlist)

        # Get the first turn!
        self.getTurn()
    
    # Saves information in the stats database.
    # nick = case-sensitive nick.
    # stype = wins/losses/quits/idleouts/kills
    #         fights/accepts/joins
    #         praises
    def countStat(self, nick, stype, add=1):
        if not self.deathmatch and not self.versusone:
            return

        try:
            nick = self.accounts[nick]
        except KeyError:  # User vanished from earth
            return
        try:
            stat = PlayerStats.get(PlayerStats.name == nick)
        except PlayerStats.DoesNotExist:
            stat = PlayerStats.create(name=nick)

        PlayerStats.update(**{stype: getattr(stat, stype) + add}).where(PlayerStats.name == nick).execute()
    
    def getStats(self, nick):
        try:
            return PlayerStats.get(PlayerStats.name ** nick)
        except:
            return False

    def top_dongers(self, bottom=False):
        players = PlayerStats.select().where((PlayerStats.matches + PlayerStats.deathmatches) >= 15)
        if bottom:
            players = players.order_by(PlayerStats.elo.asc())
        else:
            players = players.order_by(PlayerStats.elo.desc())

        return players
    
    def getTurn(self):
        if self.deathmatch or self.versusone:
            self.currgamerecord.turns += 1

        # Step 1: Check for alive players.
        aliveplayers = 0
        # TODO: Do this in a neater way
        for p in self.players:
            if self.players[p]['hp'] > 0:
                aliveplayers += 1
                survivor = p

        if aliveplayers == 1:  # one survivor, end game.
            self.win(survivor)
            return

        [self.countStat(pl, "turns") for pl in self.players]
        # Step 2: next turn
        self.currentTurn += 1
        # Check if that player exists.
        if len(self.turnlist) <= self.currentTurn:
            self.currentTurn = 0

        if self.players[self.turnlist[self.currentTurn].lower()]['hp'] > 0:  # it's alive!
            self.turnStart = time.time()
            self.poke = False
            self.message(self.channel, "It's \002{0}\002's turn.".format(self.turnlist[self.currentTurn]), message_type='m.text')
            self.players[self.turnlist[self.currentTurn].lower()]['gdr'] = 1
            if self.turnlist[self.currentTurn] == self.client.user_id:
                self.processAI()
        else:  # It's dead, try again.
            self.getTurn()

    def processAI(self):
        myself = self.players[self.client.user_id.lower()]
        # 1 - We will always hit a player with LESS than 25 HP.
        for i in self.players:
            if i == self.client.user_id.lower():
                continue
            if self.players[i]['hp'] > 0 and self.players[i]['hp'] < 25:
                self.message(self.channel, "!hit {0}".format(self.players[i]['nick']))
                self.hit(self.client.user_id, self.players[i]['nick'])
                return

        if myself['hp'] < 44 and myself['heals']:
            self.message(self.channel, "!heal")
            self.heal(self.client.user_id)
        else:
            players = self.turnlist[:]
            players.remove(self.client.user_id)
            victim = {}
            while not victim:  # !!!
                hitting = self.players[random.choice(players).lower()]
                if hitting['hp'] > 0:
                    victim = hitting
            self.message(self.channel, "!hit {0}".format(victim['nick']))
            self.hit(self.client.user_id, victim['nick'])
    
    def heal(self, target, critical=False):
        if not self.players[target.lower()]['heals'] and not critical:
            self.message(self.channel, "You can't heal this turn (but it's still your turn)")
            return

        # The max amount of HP you can recover in a single turn depends on how many times you've
        # healed since !hitting. The max number goes down, until you're forced to hit.
        healing = random.randint(22, 44 - (5 - self.players[target.lower()]['heals']) * 4)

        if critical:  # If critical heal, override upper healing limit (re roll)
            healing = random.randint(44, 88)  # (regular healing*2)

        if (healing + self.players[target.lower()]['hp']) > 100:  # If healing would bring the player over 100 HP, just set it to 100 HP
            self.players[target.lower()]['hp'] = 100
        else:
            self.players[target.lower()]['hp'] += healing

        if not critical:
            self.players[target.lower()]['heals'] -= 1

        if not critical:
            self.countStat(target, "heals")

        self.countStat(target, "totheal", healing)

        if self.deathmatch or self.versusone:  # stats
            if target.lower() == self.currgamerecord.player1:
                self.currgamerecord.player1_heals += 1
                self.currgamerecord.player1_totheal += healing
                if critical:
                    self.currgamerecord.player1_praiseroll = healing
            else:
                self.currgamerecord.player2_heals += 1
                self.currgamerecord.player2_totheal += healing
                if critical:
                    self.currgamerecord.player2_praiseroll = +healing

        self.message(self.channel, "\002{0}\002 heals for \002{1}HP\002, bringing them to \002{2}HP\002".format(
            target, healing, self.players[target.lower()]['hp']))
        self.getTurn()

    def hit(self, source, target, critical=False):
        # Rolls.
        instaroll = random.randint(1, 75) if not self.versusone else 666
        critroll = random.randint(1, 12) if not critical else 1
        damage = random.randint(18, 35)

        if instaroll == 1:
            self.ascii("INSTAKILL", lineformat="\00304")
            # remove player
            self.death(target, source)
            self.getTurn()
            return
        if critroll == 1:
            damage *= 2
            if not critical:  # If it's not a forced critical hit (via !praise), then announce the critical
                self.ascii("CRITICAL")
                self.countStat(source, "crits")
        else:
            if not self.players[target.lower()]['gdr'] == 1:
                damage = int(damage / (self.players[target.lower()]['gdr'] * self.gdrmodifier))

        # In case player is hitting themselves
        sourcehealth = self.players[source.lower()]['hp']

        self.players[source.lower()]['heals'] = 5
        self.players[target.lower()]['hp'] -= damage
        self.players[target.lower()]['gdr'] += 1
        self.countStat(source, "hits")
        self.countStat(source, "totdmg", damage)

        if self.deathmatch or self.versusone:  # stats
            if source.lower() == self.currgamerecord.player1:
                self.currgamerecord.player1_hits += 1
                self.currgamerecord.player1_totdmg += damage
                if critroll == 1:
                    self.currgamerecord.player1_crits += 1
                if critical:
                    self.currgamerecord.player1_praiseroll = -damage
            else:
                self.currgamerecord.player2_hits += 1
                self.currgamerecord.player2_totdmg += damage
                if critroll == 1:
                    self.currgamerecord.player2_crits += 1
                if critical:
                    self.currgamerecord.player2_praiseroll = -damage

        self.message(self.channel, "\002{0}\002 (\002{1}\002HP) deals \002{2}\002 damage to \002{3}\002 (\002{4}\002HP)".format(
            source, sourcehealth, damage, target, self.players[target.lower()]['hp']))

        if self.players[target.lower()]['hp'] <= 0:
            self.death(target, source)

        self.getTurn()

    def death(self, victim, slayer):
        if self.deathmatch or self.versusone:
            if victim == self.currgamerecord.player1:
                self.currgamerecord.winner = 2
            else:
                self.currgamerecord.winner = 1
        #self.set_mode(self.channel, "-v", victim)

        if self.players[victim.lower()]['hp'] <= -50:
            self.ascii("BRUTAL")
        if self.players[victim.lower()]['hp'] <= -40:
            self.ascii("SAVAGE")

        self.ascii("REKT" if random.randint(0, 39) else "RELT")  # Because 0 is false. The most beautiful line ever written.

        self.players[victim.lower()]['hp'] = -1
        self.message(self.channel, "\002{0}\002 REKT {1}".format(slayer, victim))

        if slayer != self.client.user_id:
            self.countStat(victim, "losses")

        if self.deathmatch:
            self.akick(victim)

        if victim != self.client.user_id:
            self.kick(self.channel, victim, "REKT")
    

    def kick(self, channel, victim, reason):
        try:
            self.client.api.kick_user(channel, victim, reason)
            self.client.api.invite_user(channel, victim)
        except:  # sometimes we cannot kick because the target has privileges...
            pass
    
    def akick(self, victom):
        pass  # TODO: timed bans

    def win(self, winner, realwin=True):
        losers = [self.players[player]['nick'] for player in self.players if self.players[player]['hp'] <= 0]
        
        # Reset fight-related variables
        self.deathmatch = False
        self.versusone = False
        self.gameRunning = False
        self.turnStart = 0
        self.players = {}
        self.turnlist = []
        self.accountlist = []
        self.currentTurn = -1

        # Clean everything up.
        self.restore_room()
        
        if len(self.turnlist) > 2 and realwin:
            self.message(self.channel, "{0} REKT {1}".format(self.players[winner]['nick'], ", ".join(losers)).upper())
        # Realwin is only ever false if there's a coward quit.
        if realwin:
            if losers != [self.client.user_id]:
                self.countStat(winner, "wins")

        if (self.client.user_id in losers and len(losers) == 1) or self.client.user_id == self.players[winner]['nick']:
            # Set a time so you have to wait a number of seconds
            # before the bot is available to fight again (to prevent
            # people not being able to play due to someone spamming a
            # fight against the bot).
            self.lastbotfight = time.time()

        if self.deathmatch or self.versusone:
            self.currgamerecord.save()
            # calculate ELO
            player1 = PlayerStats.get(PlayerStats.name == self.accounts[winner])
            player2 = PlayerStats.get(PlayerStats.name == self.accounts[losers[0]])

            r1 = 10 ** (player1.elo / 400)
            r2 = 10 ** (player2.elo / 400)

            e1 = r1 / (r1 + r2)
            e2 = r2 / (r1 + r2)

            k1 = 30 if (player1.matches + player1.deathmatches) < 20 else 20
            k2 = 30 if (player2.matches + player2.deathmatches) < 20 else 20

            if self.deathmatch:
                k1 += 5
                k2 += 5

            player1.elo = int(round(player1.elo + k1 * (1 - e1), 0))
            player2.elo = int(round(player2.elo + k2 * (0 - e2), 0))
            player1.save()
            player2.save()

    def chunks(self, l, n):
        """Yield successive n-sized chunks from l."""
        for i in range(0, len(l), n):
            yield l[i:i + n]

    def message(self, target, message, p_html=False, message_type='m.notice'):
        """ Compatibility layer for porting IRC modules """
        print(message)
        if "\002" in message or "\003" in message or "\x1f" in message or "\x1d" in message or p_html or re.search('@[a-zA-Z0-0.-_]+:[a-z0-0.-]+', message):
            # transform from IRC to HTML and send..
            if not p_html:
                message = html.escape(message)
            message = re.sub('\002(.*?)\002', '<b>\\1</b>', message)
            message = re.sub('\x1f(.*?)\x1f', '<u>\\1</u>', message)
            message = re.sub('\x1d(.*?)\x1d', '<i>\\1</i>', message)
            def replcolor(m):
                return '<font color="{0}">{1}</font>'.format(IRC_COLOR_MAP[m.group(1)], m.group(2))
            message = re.sub(r'\003(\d{1,2})(.*?)\003', replcolor, message)
            def repltag(m):
                return '<a href="https://matrix.to/#/{0}">{1}</a>'.format(m.group(0), self.users[m.group(0)])
            message = re.sub('@[a-zA-Z0-0.-_]+:[a-z0-0.-]+', repltag, message)

            return self.html_message(target, message, message_type)
                    
        self.client.api.send_message_event(room_id=target, event_type='m.room.message',
                                           content={'body': message, 'msgtype': message_type})


    def html_message(self, target, message, message_type='m.notice'):
        """ Sends an HTML message """
        stripped = re.sub('<[^<]+?>', '', html.unescape(message))

        self.client.api.send_message_event(room_id=target, event_type='m.room.message',
                                           content={'formatted_body': message, 'format': 'org.matrix.custom.html',
                                                    'body': stripped, 'msgtype': message_type})

    def getRoomMembers(self, room):
        users = self.client.api.get_room_members(room)
        # print(users)
        f_us = {}
        f_ud = {}
        for us in users['chunk']:
            if us['type'] != 'm.room.member' or us['content'].get('membership') != 'join':
                continue
            f_us[us['user_id']] = us['user_id']
            f_us[us['user_id'][1:].split(':')[0]] = us['user_id']
            f_us[us['content']['displayname']] = us['user_id']
            f_us[us['content']['displayname'].lower()] = us['user_id']
            f_ud[us['user_id']] = us['content']['displayname']
        return (f_us, f_ud)
    
    def ascii(self, key, font='smslant', lineformat=""):
        def repltag(m):
                return self.users[m.group(0).lower()].upper()
        key = re.sub('@[a-zA-Z0-0.-_]+:[A-Z0-0.-]+', repltag, key)
        try:
            if not config['show-ascii-art-text']:
                self.message(self.channel, key)
                return ''
        except KeyError:
            logging.warning("Plz set the show-ascii-art-text config. kthx")
        lines = [lineformat + name for name in Figlet(font).renderText(key).split("\n")[:-1] if name.strip()]
        self.html_message(self.channel, '<pre><code>' + "\n".join(lines) + '</code></pre>')

    def _timeout(self):
        while True:
            time.sleep(5)

            if not self.gameRunning or (self.turnStart == 0):
                for i in copy.copy(self.pendingFights):
                    if (time.time() - self.pendingFights[i]['ts'] > 300):
                        self.message(self.channel, "\002{0}\002's challenge has expired.".format(self.pendingFights[i]['players'][0]))
                        del self.pendingFights[i]
                continue

            if (time.time() - self.turnStart > 50) and len(self.turnlist) >= (self.currentTurn + 1):
                self.message(self.channel, "\002{0}\002 forfeits due to idle.".format(self.turnlist[self.currentTurn]), message_type='m.text')
                self.players[self.turnlist[self.currentTurn].lower()]['hp'] = -1
                self.countStat(self.turnlist[self.currentTurn], "idleouts")
                self.kick(self.channel, self.turnlist[self.currentTurn], "WAKE UP SHEEPLE")

                aliveplayers = 0
                # TODO: Do this in a neater way
                for p in self.players:
                    if self.players[p]['hp'] > 0:
                        aliveplayers += 1
                        survivor = p

                if aliveplayers >= 1:
                    self.win(survivor, False)
                else:
                    self.getTurn()
            elif (time.time() - self.turnStart > 35) and len(self.turnlist) >= (self.currentTurn + 1) and not self.poke:
                self.poke = True
                self.message(self.channel, "Wake up, \002{0}\002!".format(self.turnlist[self.currentTurn]), message_type='m.text')
    
    def import_extcmds(self):
        self.cmdhelp = {}
        try:
            self.extcmds = config['extendedcommands']
        except KeyError:
            self.extcmds = []
            logging.warning("No extended commands found in config.json")
        logging.info("Beginning extended command tests")
        self.cmds = {}
        for command in self.extcmds:
            try:  # Let's test these on start...
                cmd = importlib.import_module('extcmd.{}'.format(command))
                logging.info('Loading extended command: {}'.format(command))

                try:  # Handling non-existent helptext
                    self.cmdhelp[command] = cmd.helptext
                except AttributeError:
                    logging.warning('No helptext provided for command {}'.format(command))
                    self.cmdhelp[command] = 'A mystery'
                self.cmds[command] = cmd
            except ImportError:
                logging.warning("Failed to import specified extended command: {}".format(command))
                self.extcmds.remove(command)
                logging.warning("Removed command {} from list of available commands. You should fix config.json to remove it from there, too (or just fix the module).".format(command))
        logging.info('Finished loading all the extended commands')


# Database stuff
database = peewee.SqliteDatabase('dongerdong.db')
database.connect()


class BaseModel(peewee.Model):
    class Meta:
        database = database


class PlayerStats(BaseModel):
    name = peewee.CharField()

    turns = peewee.IntegerField(default=0)
    hits = peewee.IntegerField(default=0)
    heals = peewee.IntegerField(default=0)
    praises = peewee.IntegerField(default=0)
    totdmg = peewee.IntegerField(default=0)
    totheal = peewee.IntegerField(default=0)
    crits = peewee.IntegerField(default=0)

    elo = peewee.IntegerField(default=1300)

    matches = peewee.IntegerField(default=0)
    deathmatches = peewee.IntegerField(default=0)

    wins = peewee.IntegerField(default=0)
    losses = peewee.IntegerField(default=0)
    quits = peewee.IntegerField(default=0)
    idleouts = peewee.IntegerField(default=0)

    firstplayed = peewee.DateTimeField(default=datetime.datetime.now)
    lastplayed = peewee.DateTimeField()

    def save(self, *args, **kwargs):
        self.lastplayed = datetime.datetime.now()
        return super(PlayerStats, self).save(*args, **kwargs)

    @classmethod
    def custom_init(cls):
        database.execute_sql('create unique index if not exists playerstats_unique '
                             'on playerstats(name collate nocase)', {})


class GameStats(BaseModel):
    time = peewee.DateTimeField(default=datetime.datetime.now)
    player1 = peewee.CharField()
    player2 = peewee.CharField()

    turns = peewee.IntegerField(default=0)
    winner = peewee.IntegerField(default=0)  # 1 if player1 won, 2 if player2.

    player1_hits = peewee.IntegerField(default=0)
    player2_hits = peewee.IntegerField(default=0)

    player1_heals = peewee.IntegerField(default=0)
    player2_heals = peewee.IntegerField(default=0)

    player1_praise = peewee.IntegerField(default=0)  # 0 if no praise, 1 if player on self, 2 if player on enemy
    player1_praiseroll = peewee.IntegerField(default=0)  # positive if heal, negative if hit.

    player2_praise = peewee.IntegerField(default=0)
    player2_praiseroll = peewee.IntegerField(default=0)

    player1_totdmg = peewee.IntegerField(default=0)
    player1_totheal = peewee.IntegerField(default=0)

    player2_totdmg = peewee.IntegerField(default=0)
    player2_totheal = peewee.IntegerField(default=0)

    player1_crits = peewee.IntegerField(default=0)
    player2_crits = peewee.IntegerField(default=0)

    @classmethod
    def custom_init(cls):
        database.execute_sql('create index if not exists gamestats_unique '
                             'on gamestats(player1 collate nocase, player2 collate nocase)', {})


PlayerStats.create_table(True)
GameStats.create_table(True)

try:
    PlayerStats.custom_init()
    GameStats.custom_init()
except:
    pass


cli = DongerDong()
cli.connect()