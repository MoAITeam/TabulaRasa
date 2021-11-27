import json
import multiprocessing
from multiprocessing import managers
import socket
import sys
import random
import math
import time
from multiprocessing import Manager, Pool,Process

victoryWeight = 5000
currDepthLimit = 4
time_start = 0
timeout = 50
player = 'WHITE'
color_eval = 1
moves = {}
kingmoves = {}
killz = {}

citadel = ((0,3),(0,4),(0,5),(1,4),(3,0),(3,8),(4,0),(4,1),(5,0),(4,7),(4,8),(5,8),(8,3),(8,4),(8,5),(7,4))
walls = ((0,3),(0,5),(1,4),(3,0),(3,8),(4,1),(5,0),(4,7),(5,8),(8,3),(8,5),(7,4),(4,4))
strongholds = citadel+((4,4),)
kingdistance = {(0,0):0,(0,1):0,(0,2):0,(0,6):0,(0,7):0,(0,8):0,(1,0):0,(1,8):0,(2,0):0,(2,8):0,(6,0):0,(6,8):0,(7,0):0,(7,8):0,(8,0):0,(8,1):0,(8,2):0,(8,6):0,(8,7):0,(8,8):0,(1,1):1,(1,2):1,(1,3):2,(1,5):2,(1,6):1,(1,7):1,(2,1):1,(2,2):2,(2,3):3,(2,4):4,(2,5):3,(2,6):2,(2,7):1,(3,1):2,(3,2):3,(3,3):4,(3,4):5,(3,5):4,(3,6):3,(3,7):2,(4,2):4,(4,3):5,(4,5):5,(4,6):4,(7,1):1,(7,2):1,(7,3):2,(7,5):2,(7,6):1,(7,7):1,(6,1):1,(6,2):2,(6,3):3,(6,4):4,(6,5):3,(6,6):2,(6,7):1,(5,1):2,(5,2):3,(5,3):4,(5,4):5,(5,5):4,(5,6):3,(5,7):2,(4,4):6}
letters = ['a','b','c','d','e','f','g','h','i']

ones =                  int(0b111111111111111111111111111111111111111111111111111111111111111111111111111111111)
strongholds_bit =       int(0b000111000000010000000000000100000001110010011100000001000000000000010000000111000)
strongholds_bit_left =  int(0b000111000000010000000000000000000001000010011000000001000000000000010000000111000)
strongholds_bit_right = int(0b000111000000010000000000000100000000110010000100000000000000000000010000000111000)
strongholds_bit_up    = int(0b000000000000000000000000000100000001110010011100000001000000000000010000000111000)
strongholds_bit_down  = int(0b000111000000010000000000000100000001110010011100000001000000000000000000000000000)
vertical_kill =         int(0b011111111111111111011111111111111111111111111111111111111111111111111111111111111)
vertical_kill_dict = {}
horizontal_kill =       int(0b010111111111111111111111111111111111111111111111111111111111111111111111111111111)
king_throne_kill=       int(0b111111111111111111111111111111101111111010111111101111111111111111111111111111111)
horizontal_kill_dict = {}
king_left_throne_kill=  int(0b111111111111111111111111111111011111110111111111011111111111111111111111111111111)
king_right_throne_kill= int(0b111111111111111111111111111111110111111111011111110111111111111111111111111111111)
king_up_throne_kill=    int(0b111111111111111111111101111111010111111111111111111111111111111111111111111111111)
king_down_throne_kill=  int(0b111111111111111111111111111111111111111111111111010111111101111111111111111111111)
strongholds_bit      =  int(0b000111000000010000000000000100000001110010011100000001000000000000010000000111000)
rightborder          =  int(0b100000000100000000100000000100000000100000000100000000100000000100000000100000000)
leftborder           =  int(0b1000000001000000001000000001000000001000000001000000001000000001000000001000000001)
downborder           =  int(0b111111111000000000000000000000000000000000000000000000000000000000000000000000000)
upborder             =  int(0b111111111000000000000000000000000000000000000000000000000000000000000000000000000000000000)
coord = {}
vals = {}
strongholds_dict = {}
up_victories         =  {}
down_victories       =  {}
right_victories      =  {}
left_victories       =  {}

for i in range(0,9):
    for j in range(0,9):
        coord[2**((8-j)+9*(8-i))]=(i,j)
        strongholds_dict[2**((8-j)+9*(8-i))] = strongholds_bit
        vals[(i,j)] = 2**((8-j)+9*(8-i))

strongholds_dict[2**((8-3)+9*(8-0))] = strongholds_bit_up
strongholds_dict[2**((8-4)+9*(8-0))] = strongholds_bit_up
strongholds_dict[2**((8-5)+9*(8-0))] = strongholds_bit_up
strongholds_dict[2**((8-4)+9*(8-1))] = strongholds_bit_up
strongholds_dict[2**((8-0)+9*(8-3))] = strongholds_bit_left
strongholds_dict[2**((8-0)+9*(8-4))] = strongholds_bit_left
strongholds_dict[2**((8-0)+9*(8-5))] = strongholds_bit_left
strongholds_dict[2**((8-1)+9*(8-4))] = strongholds_bit_left
strongholds_dict[2**((8-8)+9*(8-3))] = strongholds_bit_right
strongholds_dict[2**((8-8)+9*(8-4))] = strongholds_bit_right
strongholds_dict[2**((8-8)+9*(8-5))] = strongholds_bit_right
strongholds_dict[2**((8-7)+9*(8-4))] = strongholds_bit_right
strongholds_dict[2**((8-3)+9*(8-8))] = strongholds_bit_down
strongholds_dict[2**((8-4)+9*(8-8))] = strongholds_bit_down
strongholds_dict[2**((8-5)+9*(8-8))] = strongholds_bit_down
strongholds_dict[2**((8-4)+9*(8-7))] = strongholds_bit_down



tmp_vertical_kill = vertical_kill
for i in range(1,8):
    for j in range(0,9):
        vertical_kill_dict[2**((8-j)+9*(8-i))] = vertical_kill
        vertical_kill = (vertical_kill >> 1) + 2**(80)

tmp_horizontal_kill = horizontal_kill
for i in range(0,9):
    for j in range(1,8):
        horizontal_kill_dict[2**((8-j)+9*(8-i))] = horizontal_kill
        horizontal_kill = (horizontal_kill >> 1) + 2**(80)
    horizontal_kill = (horizontal_kill >> 1) + 2**(80)
    horizontal_kill = (horizontal_kill >> 1) + 2**(80)

king_capture_dict = {}
king_close_dict = {}

for i in range(1,8):
    for j in range(1,8):
        none = 0
        up = 2**((8-j)+9*(8-i)) << 9
        down = 2**((8-j)+9*(8-i)) >> 9
        left = 2**((8-j)+9*(8-i)) << 1
        right = 2**((8-j)+9*(8-i)) >> 1
        king_capture_dict[none] = 0
        king_capture_dict[up] = 1
        king_capture_dict[down] = 1
        king_capture_dict[left] = 1
        king_capture_dict[right] = 1
        king_capture_dict[up+down] = 2
        king_capture_dict[up+left] = 2
        king_capture_dict[up+right] = 2
        king_capture_dict[down+left] = 2
        king_capture_dict[down+right] = 2
        king_capture_dict[left+right] = 2
        king_capture_dict[up+down+left] = 3
        king_capture_dict[up+down+right] = 3
        king_capture_dict[up+left+right] = 3
        king_capture_dict[down+left+right] = 3
        king_capture_dict[up+down+left+right] = 4
        king_close_dict[2**((8-j)+9*(8-i))] = up+down+left+right

for i in range(0,9):
    for j in range(0,9):
        cell = 2**((8-j)+9*(8-i))
        #dx
        newcell = cell >> 1
        rightmask = 0
        while newcell>0 and newcell & rightborder == 0:
            rightmask += newcell
            newcell = newcell >> 1
        # sx
        newcell = cell << 1
        leftmask = 0
        while newcell<2417851639229258349412352 and newcell & leftborder == 0:
            leftmask += newcell
            newcell = newcell << 1
        # down
        newcell = cell >> 9
        downmask = 0
        while newcell>0 and newcell & downborder == 0:
            downmask += newcell
            newcell = newcell >> 9
        # up
        newcell = cell << 9
        upmask = 0
        while newcell<2417851639229258349412352 and newcell & upborder == 0:
            upmask += newcell
            newcell = newcell << 9
        
        up_victories[cell] = upmask
        down_victories[cell] = downmask
        left_victories[cell] = leftmask
        right_victories[cell] = rightmask

# inglobo le kill vicino al trono in quelle verticali e orizzontali
horizontal_king_kill_dict = horizontal_kill_dict.copy()
vertical_king_kill_dict = vertical_kill_dict.copy()
horizontal_king_kill_dict[2**((8-4)+9*(8-4))] = king_throne_kill
vertical_king_kill_dict[2**((8-4)+9*(8-4))] = king_throne_kill
horizontal_king_kill_dict[2**((8-4)+9*(8-3))] = king_up_throne_kill
vertical_king_kill_dict[2**((8-4)+9*(8-3))] = king_up_throne_kill
horizontal_king_kill_dict[2**((8-4)+9*(8-5))] = king_down_throne_kill
vertical_king_kill_dict[2**((8-4)+9*(8-5))] = king_down_throne_kill
horizontal_king_kill_dict[2**((8-5)+9*(8-4))] = king_right_throne_kill
vertical_king_kill_dict[2**((8-5)+9*(8-4))] = king_right_throne_kill
horizontal_king_kill_dict[2**((8-4)+9*(8-4))] = king_left_throne_kill
vertical_king_kill_dict[2**((8-4)+9*(8-4))] = king_left_throne_kill

def convertState(state):
    kingpos = (4,4)
    king = 0
    board = state['board']
    white = 0
    black = 0
    whitevec = {}
    blackvec = {}
    whiteboard = 0
    blackboard = 0
    for i,row in enumerate(board):
        for j,cell in enumerate(row):
            if cell == 'WHITE' or cell=='KING':
                white+=1
                val = 2**((8-j)+9*(8-i))
                whitevec[val]=(i,j)
                whiteboard+=val
                if cell == 'KING':
                    kingpos = (i,j)
                    king = val
            if cell == 'BLACK':
                black +=1
                val = 2**((8-j)+9*(8-i))
                blackvec[val]=(i,j)
                blackboard+=val
    return {'turn':state['turn'],'whites':white,'blacks':black,'blackvec':blackvec,'whitevec':whitevec,'whiteboard':whiteboard,'blackboard':blackboard,'king':king,'kingpos':kingpos}

def frittoMistoWTF(state): # fritto
    count = 0
    kingpos = state['kingpos']
    for piece in state['blackvec']:
        if (coord[piece][1]-kingpos[1]+coord[piece][0]-kingpos[0]) in (1,-1):
            count += 1
    for piece in citadel:
        if (piece[1]-kingpos[1]+piece[0]-kingpos[0]) in (1,-1):
            count += 1
    return count

def expandState(state):
    color = state['turn']
    king = state['king']
    blackboard = state['blackboard']
    whiteboard = state['whiteboard']
    checkers = blackboard | whiteboard
    actions = []
    if color=='WHITE':
        for piece in state['whitevec']:
            illegal_right = strongholds_dict[piece] | checkers | rightborder
            illegal_left = strongholds_dict[piece] | checkers | leftborder
            illegal_up = strongholds_dict[piece] | checkers | upborder
            illegal_down = strongholds_dict[piece] | checkers | downborder
            if piece == king:
                # re dx
                newking = king >> 1
                while newking>0 and newking & illegal_right == 0:
                    actions.append({'from':coord[king],'to':coord[newking]})
                    newking = newking >> 1
                #re sx
                newking = king << 1
                while newking & illegal_left == 0:
                    actions.append({'from':coord[king],'to':coord[newking]})
                    newking = newking << 1
                #re down
                newking = king >> 9
                while newking>0 and newking & illegal_down == 0:
                    actions.append({'from':coord[king],'to':coord[newking]})
                    newking = newking >> 9
                #re up
                newking = king << 9
                while  newking & illegal_up == 0:
                    actions.append({'from':coord[king],'to':coord[newking]})
                    newking = newking << 9
            else:
                # dx
                newcell = piece >> 1
                while newcell>0 and newcell & illegal_right == 0:
                    actions.append({'from':coord[piece],'to':coord[newcell]})
                    newcell = newcell >> 1
                # sx
                newcell = piece << 1
                while newcell & illegal_left == 0:
                    actions.append({'from':coord[piece],'to':coord[newcell]})
                    newcell = newcell << 1
                # down
                newcell = piece >> 9
                while newcell>0 and newcell & illegal_down == 0:
                    actions.append({'from':coord[piece],'to':coord[newcell]})
                    newcell = newcell >> 9
                # up
                newcell = piece << 9
                while newcell & illegal_up == 0:
                    actions.append({'from':coord[piece],'to':coord[newcell]})
                    newcell = newcell << 9

    if color=='BLACK':
        for piece in state['blackvec']:
            illegal_right = strongholds_dict[piece] | checkers | rightborder
            illegal_left = strongholds_dict[piece] | checkers | leftborder
            illegal_up = strongholds_dict[piece] | checkers | upborder
            illegal_down = strongholds_dict[piece] | checkers | downborder
            # dx
            newcell = piece >> 1
            while newcell>0 and newcell & illegal_right == 0:
                actions.append({'from':coord[piece],'to':coord[newcell]})
                newcell = newcell >> 1
            # sx
            newcell = piece << 1
            while newcell & illegal_left == 0:
                actions.append({'from':coord[piece],'to':coord[newcell]})
                newcell = newcell << 1
            # down
            newcell = piece >> 9
            while newcell>0 and newcell & illegal_down == 0:
                actions.append({'from':coord[piece],'to':coord[newcell]})
                newcell = newcell >> 9
            # up
            newcell = piece << 9
            while newcell & illegal_up == 0:
                actions.append({'from':coord[piece],'to':coord[newcell]})
                newcell = newcell << 9

    return actions

def evaluate(state,depth):
    victoryColor=0
    capt = 0
    obstacles = state['blackboard'] | state['whiteboard'] | strongholds_bit
    king_enemies = state['blackboard'] | strongholds_bit 
    king = state['king']
    if (state['turn']=='BLACKWIN'):
        victoryColor = -1
    elif (state['turn']=='WHITEWIN'):
        victoryColor = 1
    else:
        capt=-147*king_capture_dict[(king_close_dict[king]&king_enemies)]
    whites = 250*state['whites']
    blacks = -164*state['blacks']
    manhattan = 42*(6-kingdistance[state['kingpos']])
    bonus = victoryColor*victoryWeight*((currDepthLimit - depth)/currDepthLimit+1)
    roads = 195*((1 if up_victories[king]&obstacles==0 else 0)+(1 if down_victories[king]&obstacles==0 else 0)+(1 if left_victories[king]&obstacles==0 else 0)+(1 if right_victories[king]&obstacles==0 else 0))
    v = color_eval*(manhattan+whites+blacks+roads+bonus+capt)
    return v

def checkMove(state,action):
    newturn = 'WHITE' if state['turn']=='BLACK' else 'BLACK'    
    king=state['king']
    oldcell = action['from']
    newcell = action['to']
    newwhiteboard = state['whiteboard']
    newblackboard = state['blackboard']
    newwhitevec = state['whitevec'].copy()
    newblackvec = state['blackvec'].copy()
    newkingpos = state['kingpos']
    newking = state['king']
    turn = state['turn']
    newwhite = state['whites']
    newblack = state['blacks']
    newval = vals[newcell]
    oldval = vals[oldcell]
    left = newval << 1
    right = newval >> 1
    up = newval << 9
    down = newval >> 9

    if turn == 'WHITE':
        newwhiteboard = newwhiteboard - oldval + newval
        newwhitevec.pop(oldval,None)
        newwhitevec[newval]=(i,j)
        if state['kingpos']==oldcell:
            newking = newval
            newkingpos = newcell
            if kingdistance[newkingpos] == 0:
                newturn = 'WHITEWIN'
        if (newcell[1]>1 and left & newblackboard)!=0: 
            if (horizontal_kill_dict[left] | newwhiteboard | strongholds_bit)==ones:
                newblackvec.pop(left,None)
                newblackboard = newblackboard - left
                newblack -= 1
        if (newcell[1]<7 and right & newblackboard)!=0: 
            if (horizontal_kill_dict[right] | newwhiteboard | strongholds_bit)==ones:
                newblackvec.pop(right,None)
                newblackboard = newblackboard - right
                newblack -= 1
        if (newcell[0]>1 and up & newblackboard)!=0: 
            if (vertical_kill_dict[up] | newwhiteboard | strongholds_bit)==ones:
                newblackvec.pop(up,None)
                newblackboard = newblackboard - up
                newblack -= 1
        if (newcell[0]<7 and down & newblackboard)!=0: 
            if (vertical_kill_dict[down] | newwhiteboard | strongholds_bit)==ones:
                newblackvec.pop(down,None)
                newblackboard =  newblackboard - down
                newblack -= 1
    else:
        newblackboard = newblackboard - oldval + newval
        newblackvec.pop(oldval,None)
        newblackvec[newval]=(i,j)
        if newcell[1]>1:
            if (left & king)!=0:
                if (horizontal_king_kill_dict[left] | newblackboard | strongholds_bit)==ones:
                    newwhitevec.pop(left,None)
                    newwhiteboard = newwhiteboard - left
                    newturn = 'BLACKWIN'
                    newwhite -= 1
            elif (left & newwhiteboard)!=0:
                if (horizontal_kill_dict[left] | newblackboard | strongholds_bit)==ones:
                    newwhitevec.pop(left,None)
                    newwhiteboard = newwhiteboard - left
                    newwhite -= 1
        if newcell[1]<7:
            if (right & king)!=0:
                if (horizontal_king_kill_dict[right] | newblackboard | strongholds_bit)==ones:
                    newwhitevec.pop(right,None)
                    newwhiteboard = newwhiteboard - right
                    newturn = 'BLACKWIN'
                    newwhite -= 1
            elif (right & newwhiteboard)!=0:
                if (horizontal_kill_dict[right] | newblackboard | strongholds_bit)==ones:
                    newwhitevec.pop(right,None)
                    newwhiteboard = newwhiteboard - right
                    newwhite -= 1
        if newcell[0]>1:
            if (up & king)!=0:
                if (vertical_king_kill_dict[up] | newblackboard | strongholds_bit)==ones:
                    newwhitevec.pop(up,None)
                    newwhiteboard = newwhiteboard - up
                    newturn = 'BLACKWIN'
                    newwhite -= 1
            elif (up & newwhiteboard)!=0:
                if (vertical_kill_dict[up] | newblackboard | strongholds_bit)==ones:
                    newwhitevec.pop(up,None)
                    newwhiteboard = newwhiteboard - up
                    newwhite -= 1
        if newcell[0]<7:
            if (down & king)!=0:
                if (vertical_king_kill_dict[down] | newblackboard | strongholds_bit)==ones:
                    newwhitevec.pop(down,None)
                    newwhiteboard = newwhiteboard - down
                    newturn = 'BLACKWIN'
                    newwhite -= 1
            elif (down & newwhiteboard)!=0:
                if (vertical_kill_dict[down] | newblackboard | strongholds_bit)==ones:
                    newwhitevec.pop(down,None)
                    newwhiteboard = newwhiteboard - down
                    newwhite -= 1

    return {'turn':newturn,'whites':newwhite,'blacks':newblack,'blackvec':newblackvec,'whitevec':newwhitevec,'whiteboard':newwhiteboard,'blackboard':newblackboard,'king':newking,'kingpos':newkingpos}


def maxValue(state,alpha,beta,depth,time_start):

    if ((state['turn']=='BLACKWIN') or (state['turn']=='WHITEWIN') or depth >= currDepthLimit):
        return evaluate(state, depth)

    value = -math.inf

    for action in expandState(state):
        value = max(value, minValue(checkMove(state,action), alpha, beta, depth + 1,time_start))
        if (value >= beta):
            return value
        alpha = max(alpha, value)

    return value

def minValue(state,alpha,beta,depth,time_start):

    if (depth==0):
        if(time.time()-time_start.value>timeout):
            return 0

    if ((state['turn']=='BLACKWIN') or (state['turn']=='WHITEWIN') or depth >= currDepthLimit):
        return evaluate(state, depth)

    value = math.inf

    for action in expandState(state):
        value = min(value, maxValue(checkMove(state,action), alpha, beta, depth + 1,time_start))
        if (value <= alpha):
            return value
        beta = min(beta, value)

    return value

def concurrentMinValue(a):
    state = a[0]
    alpha = a[1]
    beta = a[2]
    depth = a[3]
    action = a[4]
    return_dict = a[5]
    start = a[6]
    value = minValue(state,alpha,beta,depth,start)
    print("A={", calcJson(action['from'],action['to'],state['turn']), "}; V=", value)#, ".    CURRENT BESTS: ", possibleActions, "")
    return_dict[str(action)]=value

def randomMoveEvaluator(bestActions,state):
    
    values = []
    breaks = []
    
    for action in bestActions:
        state_recursive = state
        for i in range(100):
            if(state_recursive['turn'] in ('BLACKWIN','WHITEWIN')):
                breaks.append(i)
                break
            moves = expandState(state_recursive)
            if (len(moves) == 0):
                break
            move = random.choice(moves)
            state_recursive = checkMove(state_recursive,move)
        values.append(evaluate(state_recursive,i))
    print('bestActions: ',bestActions)
    print('long play evaluate: ', values)
    print('breaks: ', breaks)
    return bestActions[values.index(max(values))]
    
    


def calcJson(oldcell,newcell,color):
    return '{"from":"'+letters[oldcell[1]]+str(oldcell[0]+1)+'","to":"'+letters[newcell[1]]+str(newcell[0]+1)+'","turn":"'+color+'"}'

# program starts

def main():
    return sys.argv[1:]


if __name__ == '__main__':

    player,server = main()


    w = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    w.connect((server,5800 if player == 'WHITE' else 5801))
    w.send(b"\x00\x00\x00\x07")
    w.send(b"\"TbRas\"")


    if player=='WHITE':

        while True:

            # WHITE
            buf = 0
            while buf < 4:
                buf += len(w.recv(4))
            state = json.loads(w.recv(1024))

            state = convertState(state)

            color_eval = (1 if state['turn']in('WHITE','WHITEWIN') else -1)
            resultValue = -math.inf
            azioni = expandState(state)
            random.shuffle(azioni)
            result = azioni[0]

            time_start = time.time()


            possibleActions=[azioni[0]]
            values = []
            p = []

            start_1 = time.time()
        
            manager = multiprocessing.Manager()
            return_dict = manager.dict()
            start = manager.Value('start',time.time())

            with Pool(4) as p:
                p.map(concurrentMinValue, [(checkMove(state,action),-math.inf,math.inf,0,action,return_dict,start) for action in azioni])


            #for action in azioni:
            #    value =  minValue(checkMove(state,action), -math.inf, math.inf, 0)



            for action in azioni:
                value = return_dict[str(action)]

                if (value > resultValue):
                    result = action
                    possibleActions=[]
                    possibleActions.append(action)
                    resultValue = value

                elif(value == resultValue):
                    possibleActions.append(action)
                    resultValue = value

                print("A={", calcJson(action['from'],action['to'],state['turn']), "}; V=", value)#, ".    CURRENT BESTS: ", possibleActions, "")

            move = randomMoveEvaluator(possibleActions,state)


            print('Move found in',time.time()-start_1)
            #move = random.choice(possibleActions)
            moveJson = calcJson(move['from'],move['to'],state['turn'])
            w.send(len(moveJson).to_bytes(4, byteorder='big'))
            w.send(moveJson.encode())
            
            #BLACK
            buf = 0
            while buf < 4:
                buf += len(w.recv(4))
            state = json.loads(w.recv(1024))

    else:
       while True:

            buf = 0
            while buf < 4:
                buf += len(w.recv(4))
            state = json.loads(w.recv(1024))

            buf = 0
            while buf < 4:
                buf += len(w.recv(4))
            state = json.loads(w.recv(1024))

            state = convertState(state)

            color_eval = (1 if state['turn']in('WHITE','WHITEWIN') else -1)
            resultValue = -math.inf
            azioni = expandState(state)
            random.shuffle(azioni)
            result = azioni[0]

            time_start = time.time()


            possibleActions=[azioni[0]]
            values = []
            p = []

            start_1 = time.time()
        
            manager = multiprocessing.Manager()
            return_dict = manager.dict()
            start = manager.Value('start',time.time())

            with Pool(4) as p:
                p.map(concurrentMinValue, [(checkMove(state,action),-math.inf,math.inf,0,action,return_dict,start) for action in azioni])


            #for action in azioni:
            #    value =  minValue(checkMove(state,action), -math.inf, math.inf, 0)



            for action in azioni:
                value = return_dict[str(action)]

                if (value > resultValue):
                    result = action
                    possibleActions=[]
                    possibleActions.append(action)
                    resultValue = value

                elif(value == resultValue):
                    possibleActions.append(action)
                    resultValue = value

                print("A={", calcJson(action['from'],action['to'],state['turn']), "}; V=", value)#, ".    CURRENT BESTS: ", possibleActions, "")

            move = randomMoveEvaluator(possibleActions,state)


            print('Move found in',time.time()-start_1)
            #move = random.choice(possibleActions)
            moveJson = calcJson(move['from'],move['to'],state['turn'])
            w.send(len(moveJson).to_bytes(4, byteorder='big'))
            w.send(moveJson.encode())
            



            