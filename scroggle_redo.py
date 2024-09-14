from operator import itemgetter
import random
import string
import time
import collections

def make_from_file(fname):
    """
    takes a file and returns a boggle board created from it
    assumes the file contains:
        n by n single letters
        broken up by lines,
        and contains nothing else
    """
    board = []
    with open(fname) as L:
        for w in L.readlines():
            w = w.lower()
            board.append(w.strip().split())
    return board

def getListLib(fname="library.txt"):
    """
    gets the library from the file 'library.txt' - expected to be in the same folder
    Creates a dictionary that can be traversed (though slowly)
    """
    word_library = collections.defaultdict(list)
    with open(fname) as L:
        for w in L.readlines():
            word_library[w[0]].append(w.strip())
    return word_library

def getPosWords(prefix, library):
    """
    returns all the word possible with the given prefix
    """
    return [m for m in library[prefix[0]] if m.startswith(prefix)]

def createTrie(fname="library.txt"):
    """
    creates a Trie using the library 'library.txt' of words
    """
    _stop = '_stop'
    words = open(fname)
    root = dict()
    for word in words:
        word = word.strip()
        current_dict = root
        for letter in word:
            current_dict = current_dict.setdefault(letter, {})
        current_dict[_stop] = _stop
    return root

def in_trie(trie, word):
    """
    searches the Trie for a word
    """
    _stop = '_stop'
    current_dict = trie
    for letter in word:
        if letter in current_dict:
            current_dict = current_dict[letter]
        else:
            return False
    else:
        if _stop in current_dict:
            return True
        else:
            return False

def pre_in_trie(trie, prefix):
    """
    searches the Trie for a prefix to a word
    """
    global aStar_h_val
    aStar_h_val = 0
    _stop = '_stop'
    current_dict = trie
    for letter in prefix:
        if letter in current_dict:
            current_dict = current_dict[letter]
        else:
            return False
    for letter in current_dict:
        aStar_h_val += 1
    return True

def getGrid(size=4):
    """
    creates a square grid of randomly generated letters for each cell
    """
    grid = [[random.choice(string.ascii_lowercase) for c in range(size)] for r in range(size)]
    return grid

def print_grid(grid):
    """
    prints the grid to the display (for visual effects, looks nice)
    """
    for r in grid:
        for letter in r:
            print(letter, end=' ')
        print()

def getScoreLibrary(fname="values.txt"):
    """
    this function creates the dictionary for the scoring of words
    """
    letter_scores = {}
    with open(fname) as L:
        for r in L.readlines():
            rs = (r.strip()).split(' ')
            letter_scores[rs[0].lower()] = int(rs[1])
    return letter_scores

def scoreW(word):
    """
    this function takes a word and returns the score of that word
    """
    score = 0
    for w in word:
        score += scoreLib[w]
    return score

def getAdjacentLetters(grid, r, c):
    """
    grid is a list of lists (treated like a matrix), nxn size
    r = row index, c = column index
    """
    gridSize = len(grid)
    #gets the adjacent tiles (that can be moved to) from the current tile
    possMove = [ [(r-1,c-1),(r-1,c),(r-1,c+1)],      # upper 3
                  [(r,c-1), (r,c+1)],                # left and right
                    [(r+1,c-1),(r+1,c),(r+1, c+1)] ] # lower 3

    #checks for if at the edge of the grid (left/right side)
    if c == 0:
        res = [n[1:] for n in possMove]
    elif c == gridSize-1:
        res = [possMove[0][0:2], [possMove[1][0]], possMove[2][0:2]]
    else:
        res = possMove

    # checks for if at the edge of the grid (top/bottom)
    if r == 0:
        res = res[1:]
    elif r == (gridSize-1):
        res = res[0:2]
    else:
        pass

    #with indices created, makes tuples
    letters = []
    for row in res:
        letters.extend( [(grid[r][c],r,c) for r,c in row] )
    return letters

def bogPrefixEval(word):
    global bogPreDict
    if (word in bogPreDict):
        return bogPreDict[word]
    else:
        return 0

def search(grid, lib, maxM, starts, Q, hn):
    global moves
    global depth
    global depthA
    global fQ
    global fQa
    global bfact
    global aStar_h_val
    
    bfact = 0
    fQ = 0
    fQa = 0
    depth = 0
    depthA = 0
    results = set()
    frontier = starts

    if(Q and (hn > 0)):
        print("\nFrontiers sorted by heuristic values: the 5th value in the entree\n\n")

    while (moves < maxM):
        if (hn<0):
            pos = frontier[-1]
        else:
            pos = frontier[0]

        if(in_trie(lib, pos[0])):
            results.add(pos[0])
        moves += 1

        posM = getAdjacentLetters(grid, pos[1], pos[2])
        for n in posM:
            if ((n[1],n[2]) not in pos[5]):
                bfact += 1
                frontier.append( ( (pos[0] + n[0]), n[1], n[2], pos[3] + scoreW(n[0]),0,pos[5]+[(n[1],n[2])] ) )
                if (depth < len(frontier[-1][0])):
                    depth = len(frontier[-1][0])
        depthA +=  len(frontier[-1][0])
        
        if (len(frontier) > 0):
            fQa += len(frontier)
            
            if(fQ < len(frontier)):
                fQ = len(frontier)
            frontier.remove(pos)
            if(len(frontier)==0):
                return results
        else:
            print("There was no start point")
            return results

        if (hn > 0): # if A*
            i = 0
            for n in frontier:
                fn = -1
                if (n[4] != (-1)):
                    # heuristics here
                    if(pre_in_trie(lib, n[0])): # if word not possible, negates all
                        h1 = 0
                        h2 = 0
                        h3 = 0
                        h4 = 0
                        h5 = 0
                        # heuristic 1: number of letters that it could to branch
                        # off to (example; 'aa' can be followed by 5 possibilities:
                        # nothing, h, l, r, or s
                        if (hn == 1 or hn == 6 or hn == 7):
                            h1 = aStar_h_val

                        # heuristic 2: same as heuristic 1 but amplifying the impact
                        if (hn == 2 or hn == 7):
                            h2 = aStar_h_val*10

                        # heuristic 3: if the prefix is a common 'good prefix'
                        # in scroggle games
                        if (hn == 3 or hn == 7):
                            h3 = bogPrefixEval(n[0])*3

                        # heuristic 4: measures the paths to goals and finds a value via formula to represent it 
                        if (hn == 4 or hn == 6 or hn == 7):
                            if (len(n[0]) > 1):
                                avg_val = 0
                                path_val = n[3]
                                avg_len = 0
                                listOfWordsPossible = getPosWords(n[0], libD)
                                for w in listOfWordsPossible:
                                    avg_val += (scoreW(w) - path_val)
                                    avg_len += (len(w) - len(n[0]))
                                avg_val = avg_val / len(listOfWordsPossible)
                                avg_len = avg_len / len(listOfWordsPossible)
                                if (avg_len > 0):
                                    h4 = (avg_val / avg_len)
                                    if (h4 == 1 or h4 == 2):
                                        h4 = 30
                                    h4 = int(h4*10)
                                else:
                                    h4 = 1
                                    
                                if (h4 < 0): h4 = 1
                            else: h4 = 1

                        # heuristic that only adds the cost of the move, and the score so far
                        if (hn == 5):
                            h5 = 1

                        # combines the heuristic 1 and 4; searching by likelyhood and goal measuring
                        ## if hn == 6

                        # combines all the heuristics 1 through 4
                        ## if hn == 7

                        fn = (n[3] + h1 + h2 + h3 + h4 + h5) # f(n) = g(n)+h(n)

                frontier[i] = ((n[0],n[1],n[2],n[3],fn,n[5])) # updates h(n)
                i += 1
            frontier = sorted(frontier,key=itemgetter(4), reverse=True)
        
        if(Q):
            print("\nmoves: %s--" % moves, end='')
            print("Frontier length %s: " % len(frontier) , end='')
            print(frontier)
    return results

def ghcs_getWords(results, grid, library, start_point, mmoves, Q):
    """
    takes the grid, library (trie) of words, and the start point (letter, r, c) tuple
    Uses greedy hill-climbing technique
    Returns all the words that can be found from that point within max moves
    """
    def apossible(results, start_point, ignored, curWord=""):
        """
        nested recursion, searches for words using greedy hill climbing
        """
        global moves
        global fQ
        global aStar_h_val
        global bfact
        h_vals = []
        h_list = []
        if (moves < mmoves):
            if (in_trie(library, curWord)):
                results.add(curWord)
            moves += 1
            ignored.add(start_point)
            possMove = getAdjacentLetters(grid, start_point[1], start_point[2])
            candidates = [n for n in possMove if n not in ignored]
            if (Q):
                print("moves: %s" % moves)
                print("Current Frontier:", end=" ")
                print(curWord, end=" ")
                print(candidates)
            if (fQ < len(candidates)):
                fQ = len(candidates)
            for c in candidates:
                if(pre_in_trie(library, curWord + c[0])):
                    bfact += 1
                    h_vals.append(aStar_h_val)
                    h_list.append(c)
            h_list.sort(key=dict(zip(h_list, h_vals)).get, reverse=True)
            for c in h_list:
                apossible(results, c, ignored, curWord=curWord + c[0])
                if (moves < mmoves):
                    ignored.remove(c)
    apossible(results, start_point, set(), curWord=start_point[0])
    return results

def ghcs_heuristic(starts):
    """
    function that takes in the frontier and returns the frontier priority sorted using highest score first
    """
    scorez = []
    for start in starts:
        scorez.append( scoreW(start[0]) )
    starts.sort(key=dict(zip(starts, scorez)).get)
    return starts

def ghcs_solve(grid, library, starts, mmoves, Q):
    """
    organizes the results and start points of the board
    returns the final results (as a set); using A*
    """
    global bfact
    global fQ
    bfact = 0
    fQ = 0
    finalResults = set()
    starts = ghcs_heuristic(starts)
    for start in reversed(starts):
        results = ghcs_getWords(finalResults, grid, library, start, mmoves, Q)
        finalResults = finalResults.union(results)
    return finalResults

if __name__ == "__main__":
    maxM = 100        # total moves possible
    bogB = "none.txt" # default no file boggle board
    boardNum = 3      # number of boards to generate tries/stats on
    sizeG= 4          # size of the board

    # common prefixs in scroggle?
    bogPreDict = dict(a=15, an=18, anti=16, co=20, dis=20,
                      de=22,con=35,en=30,inter=15,post=22,
                      intra=15,ex=35,non=25,un=35,sym=15,
                      syn=15,sub=20, uni=20,pre=16,pro=16,
                      re=25,t=10, al=13,mi=13,my=18,pin=33,
                      ba=22,des=17,s=9,sy=11,bi=20,di=18,
                      be=19,mis=22,multi=18,il=26,im=18,
                      fore=17,am=17,go=16,deb=27,aba=30,
                      ab=27,mo=40)
    libD = getListLib() # create the dictionary
    library = createTrie() # create the dictonary as a trie
    scoreLib = getScoreLibrary() # create a dictionary for the letter scores

    if (("y") == ((input("Do you want to enter your own file boggle board? (enter 'y' or 'n'): ")).lower())):
        bogB = input("Enter the exact name of the file (assumed in same directory): ")
        maxM = int(input("How many moves do you want to allow? (example: 100): "))
        boardNum = 1
    else:
        if (("y") == ((input("Do you want to change the size/max moves/run number? (enter 'y' or 'n'): ")).lower())):
            sizeG = int(input("Enter board size (example: 4): "))
            maxM = int(input("Enter the max number of moves (example: 100): "))
            boardNum = int(input("Enter the number of runs you want to do to average boards: (example: 3): "))


    Q = False
    if (("y") == ((input("Do you want to see the steps? (enter 'y' or 'n'): ")).lower())):
        print("Node Format: word, x, y, g(n), h(n), [path]\n")
        Q = True
    
    scrz1=[0,0,0,0,0,0,0,0,0,0]
    scrz2=[0,0,0,0,0,0,0,0,0,0]
    timez=[0,0,0,0,0,0,0,0,0,0]
    bfz=[0,0,0,0,0,0,0,0,0,0]
    qz1=[0,0,0,0,0,0,0,0,0,0]
    qz2=[0,0,0,0,0,0,0,0,0]
    depths1=[0,0,0,0,0,0,0,0,0]
    depths2=[0,0,0,0,0,0,0,0,0]
    ofN = 0
    for ofn in range(0,boardNum):
        ofN += 1
        if (bogB == "none.txt"):
            grid = getGrid(sizeG)
        else:
            grid = make_from_file(bogB)
            sizeG = len(grid)
            print(grid)
        # a list of start tuples for each thing in the grid (letter, row, col) style
        starts = []
        for r,row in enumerate(grid):
            for c,letter in enumerate(row):
                starts.append( (letter, r, c) )
                
        for i in range(-1, 9):
            n_start = []
            for n in starts:
                # letter, row, col, G(n), H(n), path of (x y)
                n_start.append( (n[0],n[1],n[2],scoreW(n[0]),0,[(n[1],n[2])]))
            moves = 0
            score = 0
            tstart = time.time()
            print("\nSEARCHING with ",end="")
            if (i < 0):
                print("Depth First Search", end="")
            elif (i == 0):
                print("Breadth First Search", end="")
            elif (i==8):
                print("Greedy Hill Climbing Search", end="")
            else:
                print("A* Search", end="")
            print(" on following board:")
            if (i==1 or i==2 or i==3 or i==4 or i==5): print("   Using A* heuristic h(n)= <function is a sneakret>")
            elif (i==6): print("   Using A* heuristic h(n)= <function is two of the sneakrets>")
            elif (i==7): print("   Using A* heuristic h(n)= <function is all the sneakrets>")
            print_grid(grid)
            if(Q):
                print("moves: %s--" % moves, end='')
                print("Frontier length %s: " % len(n_start) , end='')
                print(n_start)
            if (i==8): results = ghcs_solve(grid, library, starts, maxM, Q)
            else: results = search(grid, library, maxM, n_start, Q, i)
            for n in results:
                score += scoreW(n)
            print("Search Type ", end="")
            if(i==-1):
                print("DFS", end="")
            elif(i==0):
                print("BFS", end="")
            elif(i==8):
                print("GHCS", end="")
            else:
                print("A*", end="")
            print(" for %s expansions resulted in:" % moves)
            print("%s unique words found: " % len(results), end="")
            scrz2[i+1] += len(results)
            if (len(results) > 0):
                print(sorted(results))
            else: print()
            if (i==8):
                print("Max Frontier Q size observed at once: %s" % fQ)
            else:
                print("Avg(Max) Frontier Q size: %.2f(%s)" % (fQa / moves, fQ))
                qz2[i+1] += (fQa / moves)
                print("Avg(Max) searched node depth: %.2f(%s)" % (depthA / moves, depth))
                depths1[i+1] += (depthA/moves)
                depths2[i+1] += depth
            qz1[i+1] += fQ
            print("Avg branching factor: %.2f" % (bfact/moves))
            bfz[i+1] += (bfact/moves)
            print("Scroggle score: %s" % score)
            scrz1[i+1] += score
            t = time.time() - tstart
            print("Time taken (in seconds): %.5f" % t)
            timez[i+1] += t

    print("\n\nStatistics (averaged of %s trials) for %s by %s boards with %s moves:" % (ofN,sizeG,sizeG,maxM))
    print("type  | score | found | time  | avg_bf | max_Q  |  avg_Q  | avg_depth | max depth")
    print(" DFS  | %5.1f | %5.1f |%6.3f | " % (scrz1[0]/ofN,scrz2[0]/ofN,timez[0]/ofN), end="")
    print("%6.2f | %6.1f | " % (bfz[0]/ofN,qz1[0]/ofN), end="")
    print("%6.1f  | %9.1f | %3.1f" % (qz2[0]/ofN,depths1[0]/ofN,depths2[0]/ofN))
    print(" BFS  | %5.1f | %5.1f |%6.3f | " % (scrz1[1]/ofN,scrz2[1]/ofN,timez[1]/ofN), end="")
    print("%6.2f | %6.1f | " % (bfz[1]/ofN,qz1[1]/ofN), end="")
    print("%6.1f  | %9.1f | %3.1f" % (qz2[1]/ofN,depths1[1]/ofN,depths2[1]/ofN))
    print(" A*1  | %5.1f | %5.1f |%6.3f | " % (scrz1[2]/ofN,scrz2[2]/ofN,timez[2]/ofN), end="")
    print("%6.2f | %6.1f | " % (bfz[2]/ofN,qz1[2]/ofN), end="")
    print("%6.1f  | %9.1f | %3.1f" % (qz2[2]/ofN,depths1[2]/ofN,depths2[2]/ofN))
    print(" A*2  | %5.1f | %5.1f |%6.3f | " % (scrz1[3]/ofN,scrz2[3]/ofN,timez[3]/ofN), end="")
    print("%6.2f | %6.1f | " % (bfz[3]/ofN,qz1[3]/ofN), end="")
    print("%6.1f  | %9.1f | %3.1f" % (qz2[3]/ofN,depths1[3]/ofN,depths2[3]/ofN))
    print(" A*3  | %5.1f | %5.1f |%6.3f | " % (scrz1[4]/ofN,scrz2[4]/ofN,timez[4]/ofN), end="")
    print("%6.2f | %6.1f | " % (bfz[4]/ofN,qz1[4]/ofN), end="")
    print("%6.1f  | %9.1f | %3.1f" % (qz2[4]/ofN,depths1[4]/ofN,depths2[4]/ofN))
    print(" A*4  | %5.1f | %5.1f |%6.3f | " % (scrz1[5]/ofN,scrz2[5]/ofN,timez[5]/ofN), end="")
    print("%6.2f | %6.1f | " % (bfz[5]/ofN,qz1[5]/ofN), end="")
    print("%6.1f  | %9.1f | %3.1f" % (qz2[5]/ofN,depths1[5]/ofN,depths2[5]/ofN))
    print(" A*5  | %5.1f | %5.1f |%6.3f | " % (scrz1[6]/ofN,scrz2[6]/ofN,timez[6]/ofN), end="")
    print("%6.2f | %6.1f | " % (bfz[6]/ofN,qz1[6]/ofN), end="")
    print("%6.1f  | %9.1f | %3.1f" % (qz2[6]/ofN,depths1[6]/ofN,depths2[6]/ofN))
    print("A*1+4 | %5.1f | %5.1f |%6.3f | " % (scrz1[7]/ofN,scrz2[7]/ofN,timez[7]/ofN), end="")
    print("%6.2f | %6.1f | " % (bfz[7]/ofN,qz1[7]/ofN), end="")
    print("%6.1f  | %9.1f | %3.1f" % (qz2[7]/ofN,depths1[7]/ofN,depths2[7]/ofN))
    print("all A*| %5.1f | %5.1f |%6.3f | " % (scrz1[8]/ofN,scrz2[8]/ofN,timez[8]/ofN), end="")
    print("%6.2f | %6.1f | " % (bfz[8]/ofN,qz1[8]/ofN), end="")
    print("%6.1f  | %9.1f | %3.1f" % (qz2[8]/ofN,depths1[8]/ofN,depths2[8]/ofN))
    print(" GHCS | %5.1f | %5.1f |%6.3f | " % (scrz1[9]/ofN,scrz2[9]/ofN,timez[9]/ofN), end="")
    print("%6.2f | %6.1f | " % (bfz[9]/ofN,qz1[9]/ofN), end="")
    print()
    
    print("\ntada!")
