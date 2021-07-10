from petlib.ec import EcGroup, Bn
import time
import random
import multiprocessing as mp
import math
import os
from os import path
import shutil
import binascii
import trie
from collections import Counter
import sys
import ast

CURVENUMBER = 714 #SECG curve over a 256 bit primefield ("secp256k1")
#CURVENUMBER = 716 # NIST/SECG curve over a 521 bit prime field ("secp521r1")
#CURVENUMBER = 415 # X9.62/SECG curve over a 256 bit prime field ("secp256r1")

def printProgressBar (iteration, total, prefix = '', suffix = '', decimals = 1, length = 100, fill = '█', printEnd = "\r"):
    """
    Call in a loop to create terminal progress bar
    @params:
        iteration   - Required  : current iteration (Int)
        total       - Required  : total iterations (Int)
        prefix      - Optional  : prefix string (Str)
        suffix      - Optional  : suffix string (Str)
        decimals    - Optional  : positive number of decimals in percent complete (Int)
        length      - Optional  : character length of bar (Int)
        fill        - Optional  : bar fill character (Str)
        printEnd    - Optional  : end character (e.g. "\r", "\r\n") (Str)
    """
    percent = ("{0:." + str(decimals) + "f}").format(100 * (iteration / float(total)))
    filledLength = int(length * iteration // total)
    bar = fill * filledLength + '-' * (length - filledLength)
    print('\r%s |%s| %s%% %s' % (prefix, bar, percent, suffix), end = printEnd)
    # Print New Line on Complete
    if iteration == total:
        print()

class PublicParams:
    """
    Represents system's public parameters
    ...
    Attributes
    ----------
    group : EcGroup
        Elliptic curve as defined in petlib library
    g : EcPt
        Generator g
    """
    group = EcGroup(CURVENUMBER)
    def __init__(self, g = group.generator()):

        """
        Parameters
        ----------
        g : EcPt
            Generator g
        """
        self.g = g

PP = PublicParams()

def checkDups(listOfElems):
    """Checks if a list contains any duplicates
    Parameters
    ----------
    listOfElems : list
        List to be checked
    Returns
    -------
    bool
        If there are any duplicates
    """
    setOfElems = set()
    for elem in listOfElems:
        if elem in setOfElems:
            return True
        else:
            setOfElems.add(elem)
    return False

def lookup2File(rng):
    """Generates a lookup table with range 2^rng, saves it to .txt file
    Parameters
    ----------
    rng : int
        Range of table
    Returns
    -------
    None
    """
    with open(str(CURVENUMBER)+'-'+str(rng)+'bits.txt', 'w') as filehandle:
        temp = PP.g
        for i in range(1, 2**rng):
            filehandle.write('%s\n' % str(temp))
            temp = temp + PP.g
            printProgressBar(i + 1, 2**rng, prefix = 'Progress:', suffix = 'Complete', length = 50)
    return None

def readLookFromFile(rng):
    """Loads lookup table from file formatted as XXbits.txt
    Parameters
    ----------
    rng : int
        Range of table
    Returns
    -------
    readList: list
    """
    readList = []
    with open(str(CURVENUMBER)+'-'+str(rng)+'bits.txt', 'r') as filehandle:
        filecontents = filehandle.readlines()
        for line in filecontents:
            current_place = line[:-1]
            readList.append(current_place)
    return readList

def readLookFromFileB(filename):
    """Loads lookup table from file
    Parameters
    ----------
    filename : string
        Name of file
    Returns
    -------
    readList: list
    """    
    readList = []
    with open(filename, 'r') as filehandle:
        filecontents = filehandle.readlines()
        for line in filecontents:
            current_place = line[:-1]
            readList.append(current_place)
    return readList

def lookup2FileRes(rng):
    """Generates a lookup table with range 2^rng, resuming if previous exists.
       Saves it to .txt file
    Parameters
    ----------
    rng : int
        Range of table
    Returns
    -------
    None
    """
    startIdx = 1
    r = rng
    resume = False
    while r > 7 and not resume:
        r-=1
        resume = path.exists(str(CURVENUMBER)+'-'+str(r)+'bits.txt')
    if resume:
        shutil.copy((str(CURVENUMBER)+'-'+str(r)+'bits.txt'), (str(CURVENUMBER)+'-'+str(rng)+'bits.txt'))
        startIdx = 2**r
    with open(str(CURVENUMBER)+'-'+str(rng)+'bits.txt', 'a') as filehandle:
        temp = startIdx*PP.g
        for i in range(startIdx, 2**rng):
            filehandle.write('%s\n' % str(temp))
            temp = temp + PP.g
            printProgressBar(i + 1, 2**rng, prefix = 'Progress:', suffix = 'Complete', length = 50)
    return None

def lookup2FileB(torng,fromrng=0):
    """Generates a lookup table from range 2^fromrng to 2^torng.
       Saves it to .txt file
    Parameters
    ----------
    fromrng, torng : int
        Range of table
    Returns
    -------
    None
    """
    startIdx = 2**fromrng
    with open(str(CURVENUMBER)+'-'+str(fromrng)+'to'+str(torng)+'bits.txt', 'a') as filehandle:
        temp = startIdx*PP.g
        for i in range(startIdx, 2**torng):
            filehandle.write('%s\n' % str(temp))
            temp = temp + PP.g
            printProgressBar(i + 1, 2**torng, prefix = 'Progress:', suffix = 'Complete', length = 50)
    return None

def lookup2FileC(torng,fromrng=1):
    """Generates a lookup table from range fromrng to torng.
       Saves it to .txt file
    Parameters
    ----------
    fromrng, torng : int
        Range of table
    Returns
    -------
    None
    """
    with open(str(CURVENUMBER)+'-'+str(fromrng)+'to'+str(torng)+'.txt', 'a') as filehandle:
        temp = fromrng*PP.g
        for i in range(fromrng, torng):
            filehandle.write('%s\n' % str(temp))
            temp = temp + PP.g
            printProgressBar(i + 1, torng, prefix = 'Progress:', suffix = 'Complete', length = 50)
    return None

def concatFiles(fromrng,midrng,torng):
    """Concatenates two files containing two lookup tables into a new file named "torng"
       Saves it to .txt file
    Parameters
    ----------
    fromrng, midrng torng : int
        Range of table
    Returns
    -------
    None
    """
    fileA = str(CURVENUMBER)+'-'+str(fromrng)+'to'+str(midrng)+'bits.txt'
    fileB = str(CURVENUMBER)+'-'+str(midrng)+'to'+str(torng)+'bits.txt'
    fileC = str(CURVENUMBER)+'-'+str(fromrng)+'to'+str(torng)+'bits.txt'
    with open(fileC, 'w') as outfile:
        for fname in [fileA, fileB]:
            with open(fname) as infile:
                for line in infile:
                    outfile.write(line)

def concatFilesC(fromrng,midrng,torng):
    """Concatenates two files containing two lookup tables into a new file named "torng"
       Saves it to .txt file
    Parameters
    ----------
    fromrng, midrng torng : int
        Range of table
    Returns
    -------
    None
    """
    fileA = str(CURVENUMBER)+'-'+str(fromrng)+'to'+str(midrng)+'.txt'
    fileB = str(CURVENUMBER)+'-'+str(midrng)+'to'+str(torng)+'.txt'
    fileC = str(CURVENUMBER)+'-'+str(fromrng)+'to'+str(torng)+'.txt'
    with open(fileC, 'w') as outfile:
        for fname in [fileA, fileB]:
            with open(fname) as infile:
                for line in infile:
                    outfile.write(line)

def truncate(lookupRaw):
    """Truncates lookuptable iteratively
    Parameters
    ----------
    lookupRaw : list
        List to be truncated
    Returns
    -------
    testList
        Truncated table
    """
    for i in range(1, len(lookupRaw[0])):
        testList = []
        for elem in lookupRaw:
            testList.append(elem[-i:])
        if not checkDups(testList):
            return testList

def truncNomem(inputfile,truncvalue):
    """Truncates lookuptable iteratively on the fly, output to file
    Parameters
    ----------
    inputfile : string
        Table to be truncated
    truncvalue: int
        Truncation paramener
    Returns
    -------
    None
    """
    #truncvalue in hexes
    with open(inputfile + str(".trunc"), 'w') as outfile:
        with open(inputfile) as infile:
            for line in infile:
                outfile.write(line[-truncvalue-1:])

def truncNomemleft(inputfile,truncvalue):
    """Truncates lookuptable iteratively on the fly (from the left), output to file
    Parameters
    ----------
    inputfile : string
        Table to be truncated
    truncvalue: int
        Truncation paramener
    Returns
    -------
    None
    """
    with open(inputfile + str(".truncl"), 'w') as outfile:
        with open(inputfile) as infile:
            for line in infile:
                outfile.write(line[2:2+truncvalue]+"\n")

def truncHeur(lookupRaw,target,quit=None,foundit=None):
    """Truncates lookuptable with random heuristic. Can be parallelized.
    Parameters
    ----------
    lookupRaw : list
        List to be truncated
    target : int
        Sets the difficulty of the search. Typically is 1. If set to 2 might take very long.
    quit : multiprocessing.event
        Stops loop when found solution
    foundit : multiprocessing.event
        Quits all spawned processes when found solution
    Returns
    -------
    None
    """
    #for j in range(0,tries):
    if quit == None:
        quit = mp.Event()
        foundit = mp.Event()
    i = 0
    start = time.time()
    while not quit.is_set():
        #make tries random attempts
        #pick i-1 random hex indices
        i+=1
        selInd = random.sample(range(2,66),target)
        selInd.sort(reverse=True)
        testList = []
        for elem in lookupRaw:
            #choose those random indices and test if all unique
            truncElem = ''
            for k in selInd:
                truncElem = truncElem + elem[k]
            testList.append(truncElem)
        if not checkDups(testList):
            print ("Found combination: " +str(selInd))
            print("Tries/sec:" + str(i/(time.time()-start)))
            foundit.set()
            break

def truncTest(rng,diff=1):
    """First truncates using truncate(), then truncates using truncHeur().
    Parameters
    ----------
    rng : int
        Range size to be read from file
    diff : int
        Sets the difficulty of the search. Typically is 1. If set to 2 might take very long.
    Returns
    -------
    None
    """
    f = readLookFromFile(rng)
    a1 = truncate(f) 
    print("Naive truncate:" + str(len(a1[0])))
    truncHeur(f,len(a1[0])-diff)

def truncTestMult(rng,diff=1,cores=mp.cpu_count()):
    """First truncates using truncate(), then truncates using truncHeur() using multiple cores.
    Parameters
    ----------
    rng : int
        Range size to be read from file
    diff : int
        Sets the difficulty of the search. Typically is 1. If set to 2 might take very long.
    cores : int
        Number of cores to be used
    Example: truncTestMult(1000000,2,6)
    Returns
    -------
    None
    """
    f = readLookFromFile(rng)
    a1 = truncate(f)
    print("Naive truncate:" + str(len(a1[0])))
    quit = mp.Event()
    foundit = mp.Event()
    for _ in range(cores):
        p = mp.Process(target=truncHeur, args=(f, len(a1[0])-diff, quit, foundit))
        p.start()
    foundit.wait()
    quit.set()

def truncateR(table,hexes):
    """Truncates table from MSB side.
    Parameters
    ----------
    table : list
        List to be truncated
    hexes : int
        Number of hex positions for final result.
    Returns
    -------
    truncList
        Truncated lookup table
    """
    for _ in range(1, len(table[0])):
        truncList = []
        for elem in table:
            truncList.append(elem[:hexes])
    return truncList

def returnDups(listOfElems):
    """Extracts duplicates from list.
    Parameters
    ----------
    listOfElems : list
        List to be parsed
    Returns
    -------
    [uniqueList,dupeindices]
        uniqueList : has only unique elements, None elsewhere
        dupeindices : set of duplicate indices in initial list
    """
    setOfElems = set()
    dupeindices = set()
    uniqueList = []
    for i, elem in enumerate(listOfElems):
    #for elem in listOfElems:
        if elem in setOfElems:
            uniqueList.append(None)
            dupeindices.add(i)
        else:
            setOfElems.add(elem)
            uniqueList.append(elem)
    return [uniqueList,dupeindices]

def countSizes(lst):
    """Counts number of occurences for each size.
    Parameters
    ----------
    lst : list
        List to be counted
    Returns
    -------
    counddict
        Dictionary (JSON) with counts
    """
    countdict = {}
    for elm in lst:
        if len(elm) in countdict:
            countdict[len(elm)]+=1
        else:
            countdict.update({len(elm):1})
    return countdict

def truncVar(rng):
    """Truncates using variable length.
    Parameters
    ----------
    rng : int
        Range size to be read from file
    Returns
    -------
    outList
        Truncated List
    """
    f = readLookFromFile(rng)
    a1 = truncate(f)
    print("Naive truncate: " + str(len(a1[0])) +" hexes")
    reprhexes = math.ceil(math.log(len(a1)+1,16)) -1 #minimum (ideal) hexes needed to represent
    print("Ideal truncate: " + str(reprhexes) +" hexes")
    outList = [] #unique elements will go here
    for idx in range(2**rng -1):
        outList.append(None)
    while checkNoneList(outList): #check if everything has moved in outList
        dupedict = {} #map of occurences
        tempList = truncateR(a1,reprhexes) #first truncate to minimum hexes
        for elem in tempList: #count occurences in tempList
            if elem in dupedict and elem != None:
                dupedict[elem]+=1
            elif elem != None:
                dupedict.update({elem:1})
        for idx,elem in enumerate(tempList): #move unique elements from tempList to outList
            if outList[idx] == None and dupedict[elem] == 1:
                outList[idx] = elem
        reprhexes +=1 #add another hex representation
    return outList

def lookup(lookupTable,gx):
    """
    Looks up element gx from lookupTable
    Example:
    f = readLookFromFileB("714-0to16bits.txt")
    lookup(f,'03fa8711c01451a67ab233a2e5503445216e3d663d23d2a9faf0b01889aa330249')
    """
    return (lookupTable.index(gx))

def babygiantstep(lookupTable,gx,giantstepsize):
    """
    Do baby and giant steps according to Shank's algorithm.
    Prints result to stdout.
    Parameters
    ----------
    lookipTable : list
        babystep lookuptable
    gx: string
        Value to decrypt
    giantstepsize: int
        giant step parameter beta
    Returns
    -------
    None
    """
    '''
    Examples:
    giantstep = 2**16
    str(giantstep*PP.g)
    gx = 255*PP.g
    babygiantstep(f,gx,giantstep)
    gx = 257*PP.g
    babygiantstep(f,gx,giantstep)    
    f = readLookFromFileB("714-1to65536.txt")
    lookup(f,str(14335*PP.g))
    babygiantstep(f,14335*PP.g,2**8)
    babygiantstep(f,131547*PP.g,2**8)
    '''
    i = 1
    gstp = giantstepsize*PP.g
    while i <= giantstepsize:
        try:
            res = (i-1)*giantstepsize + lookupTable.index(str(gx)) +1
            print(res)
            break
        except ValueError:
            gx = gx - gstp
            i+=1
    if i == giantstepsize+1:
        print("Not found")

def checkNoneList(lst):
    """Check if list has any None types.
    Parameters
    ----------
    lst : lst
        List to be checked
    Returns
    -------
    bool
    """
    for elem in lst:
        if elem == None:
            return True
    return False

def checkDupsFile(filename):
    """Checks if a file contains any duplicates
    Parameters
    ----------
    filehandle : string
        File to be checked
    Example: checkDupsFile("714-1to65536.txt.trunc")
    Returns
    -------
    bool
        If there are any duplicates
    """
    setOfElems = set()
    i=0
    start = time.time()
    with open(str(filename), 'r') as filehandle:
        for line in filehandle:
            #elem = bytes.fromhex(line[:-1])
            elem = line[:-1]
            if elem in setOfElems:
                print("Total time: " + str(round((time.time() - start) ,3)) + str(" sec"))
                return True
            else:
                setOfElems.add(elem)
            i+=1
            if i % 10000 ==0: print(i,end='\r',flush=True)
    print("Total time: " + str(round((time.time() - start) ,3)) + str(" sec"))
    return False

def checkDupsFileparts(numfiles,resi=1,resj=2):
    """
    Checks for duplicates across splitted files.
    Writes results to file.
    Parameters
    ----------
    numfiles : int
        number of splitted files
    resi, resj: int
        parameters used for resuming
    Returns
    -------
    None
    """
    start = time.time()
    k = 0
    for i in range(resi,numfiles+1):
        if i == resi:
            startj = resj
        else:
            startj = i+1
        for j in range(startj,numfiles+1):
            k = 0
            setOfElems = set()
            with open("part"+str(i), 'r') as filehandle:
                for line in filehandle:
                    k+=1
                    if k % 100000 ==0: print(str(i)+"-"+str(j)+"-"+str(k),end='\r',flush=True)
                    elem = line[:-1]
                    if elem in setOfElems:
                        f = open("dupsresults.txt", "a")
                        f.write(str(elem)+ "\n")
                        f.write(str(i)+"-"+str(j)+ "\n")
                        f.write(str(k)+ "\n")
                        f.close()
                    else:
                        setOfElems.add(elem)
            with open("part"+str(j), 'r') as filehandle:
                for line in filehandle:
                    k+=1
                    if k % 100000 ==0: print(str(i)+"-"+str(j)+"-"+str(k),end='\r',flush=True)
                    elem = line[:-1]
                    if elem in setOfElems:
                        f = open("dupsresults.txt", "a")
                        f.write(str(elem)+ "\n")
                        f.write(str(i)+"-"+str(j)+ "\n")
                        f.write(str(k)+ "\n")
                        f.close()
                    else:
                        setOfElems.add(elem)
            f = open("dupsresults.txt", "a")
            f.write("Completed: "+str(i)+"-"+str(j) + "\n")
            f.close()
    print("Total time: " + str(round((time.time() - start) ,3)) + str(" sec"))

def cremptyfile(filename,linenums,linelen,char=" "):
    """
    Creates an empty file with a specified number of lines.
    Parameters
    ----------
    filename : string
        filename to output
    linenums: int
        number of lines
    linelen: int
        length of each line
    char: string
        characters to fill
    Returns
    -------
    None
    """
    with open(filename, 'w') as outfile:
        for _ in range(1,linenums):
            outfile.write(char*linelen +"\n")

def checkvarDupsFileparts(numfiles,linenums,trdpth,resi=1,resj=2):
    """
    Checks for duplicates across splitted files with variable truncation.
    Writes results to file.
    Parameters
    ----------
    numfiles : int
        number of splitted files
    linenums: int
        number of lines
    trdpth: int
        truncation depth        
    resi, resj: int
        parameters used for resuming
    Returns
    -------
    None
    """
    start = time.time()
    k = 0
    with open("part1", 'r') as testfile:
        line1 = testfile.readline()
        linelgth = len(line1)
        testfile.close()
    for i in range(resi,numfiles+1):
        if i == resi:
            startj = resj
        else:
            startj = i+1
        for j in range(startj,numfiles+1):
            k = 0
            setOfElems = set()
            outfilename = "part"+str(i)+".dups"
            if not os.path.exists(outfilename):
                cremptyfile(outfilename,linenums,linelgth)
            with open("part"+str(i), 'r') as fileA,open(outfilename, 'r+') as fileB:
                line_start = fileB.tell()
                line1 = fileA.readline()[trdpth:]
                line2 = fileB.readline()
                while line1 and line2:
                    k+=1
                    if k % 100000 ==0: print(str(i)+"-"+str(j)+"-"+str(k),end='\r',flush=True)
                    elem = line1[:-1]
                    offset = 1
                    if line2[-1:] != "\n": offset = 0
                    replace = (len(line1)-offset)*"x"
                    if elem in setOfElems:
                        #if elem is duplicate
                        #put xxx's to dupsfile
                        fileB.seek(line_start)
                        fileB.write(replace) 
                    else:
                        #elem is not duplicate
                        setOfElems.add(elem)
                        if line2[:-1] != (len(line1)-offset)*"x":
                            fileB.seek(line_start)
                            fileB.write(replace)
                    line_start = fileB.tell()
                    if line1 != line2: line1 = fileA.readline()
                    line2 = fileB.readline()
            outfilename = "part"+str(j)+".dups"
            if not os.path.exists(outfilename):
                cremptyfile(outfilename,linenums,linelgth)
            with open("part"+str(j), 'r') as fileA,open("part"+str(j)+".dups", 'r+') as fileB:
                line_start = fileB.tell()
                line1 = fileA.readline()[trdpth:]
                line2 = fileB.readline()
                while line1 and line2:
                    k+=1
                    if k % 100000 ==0: print(str(i)+"-"+str(j)+"-"+str(k),end='\r',flush=True)
                    elem = line1[:-1]
                    offset = 1
                    if line2[-1:] != "\n": offset = 0
                    replace = (len(line1)-offset)*"x"
                    if elem in setOfElems:
                        #if elem is duplicate
                        #put xxx's to dupsfile
                        fileB.seek(line_start)
                        fileB.write(replace) 
                    else:
                        #elem is not duplicate
                        setOfElems.add(elem)
                        if line2[:-1] != (len(line1)-offset)*"x":
                            fileB.seek(line_start)
                            fileB.write(replace)
                    line_start = fileB.tell()
                    if line1 != line2: line1 = fileA.readline()
                    line2 = fileB.readline()
            f = open("dupsresultstr.txt", "a")
            f.write("Completed Tr: "+str(i)+"-"+str(j) + "\n")
            f.close()
    print("Total time: " + str(round((time.time() - start) ,3)) + str(" sec"))


def renameFileparts():
    """
    Renames file parts after running in linux terminal:
    $ split -l 4096 714-1to65536.txt
    """
    k=0
    for filename in sorted(os.listdir()):
        if filename.startswith("x"):
            k+=1
            org_fp = os.path.join(filename)
            new_fp = os.path.join("part"+(str(k)))
            os.rename(org_fp, new_fp)

def lookupinfile(filename,elem):
    """
    Looks up element elem in filename, outputs at stdout
    """
    with open(str(filename), 'r') as filehandle:
        for linenum, line in enumerate(filehandle):
                if elem == line[:-1]:
                    print("Element "+str(elem)+" found at line " + str(linenum+1))

def lookupvalue(filename,val):
    """
    Looks up value to be decrypted in filename, returns line number
    """
    with open(str(filename), 'r') as filehandle:
        for linenum, line in enumerate(filehandle):
                if linenum+1 == val:
                    return line[:-1]

def insert2line(inputfile,lineinsert,instring):
    """
    Inserts instring in inputfile at lineinsert
    """
    with open(inputfile + str(".insert"), 'w') as outfile:
        with open(inputfile,'r') as infile:
            for linenum,line in enumerate(infile):
                if linenum == lineinsert:
                    outfile.write(instring+"\n")
                outfile.write(line)

def countlines(filename):
    """
    Counts total number of lines, returns result
    """
    with open(str(filename), 'r') as filehandle:
        totallines = 0
        for _ in filehandle:
            totallines +=1
    return totallines

def lookup2FileResB(rng):
    """Generates a lookup table with range 2^rng, resuming if previous exists.
       Saves it to .txt file
    Parameters
    ----------
    rng : int
        Range of table (as exponent value)
    Returns
    -------
    None
    """
    outfilename = str(CURVENUMBER)+'-1to'+str(rng)+'.txt'
    resume = path.exists(outfilename)
    if resume:
        startIdx = countlines(outfilename) +1
    else:
        startIdx = 1
    with open(outfilename, 'a') as filehandle:
        temp = startIdx*PP.g
        for i in range(startIdx, rng):
            filehandle.write('%s\n' % str(temp))
            temp = temp + PP.g
            printProgressBar(i + 1, rng, prefix = 'Progress:', suffix = 'Complete', length = 50)

def lookupelemtruncl(filename,elem,truncvalue):
    """
    Looks if elem collisions exist during truncation.
    Returns linenumber if found.
    """
    with open(str(filename), 'r') as filehandle:
        for linenum, line in enumerate(filehandle):
                if elem[2:2+truncvalue] == line[:-1]:
                    return linenum+1

def babygiantsteptrunc(filename,gx,truncvalue,giantstepsize):
    """
    Run lookupelemtruncl() using Shanks as well.
    """
    i = 1
    gstp = 2**giantstepsize*PP.g
    res = None
    while i <= 2**giantstepsize and res == None:
        print(str(i)+"/"+str(2**giantstepsize),end='\r',flush=True)
        res = lookupelemtruncl(filename,str(gx),truncvalue)
        gx = gx - gstp
        i+=1
    if res == None:
        return None
    else:
        return res+(i-2)*(2**giantstepsize)

def lookupelemtrunclfileparts(elem,truncvalue):
    """
    Run lookupelemtruncl() across 16 fileparts
    (16 is recommended for typical 2^32 range)
    """
    result = None
    for i in range(1,17):
        print(i)
        if result == None:
            result = lookupelemtruncl("part"+str(i),elem,truncvalue)
            if result != None:
                return result + ((i-1)*2**28)

def hextobin(infile,outfile):
    '''
    Convert truncated hex text file to binary
    '''
    with open(str(infile), 'r') as filehandle:
        filename = open(outfile, 'ab')
        for line in filehandle:
            filename.write(binascii.unhexlify(line[:-1]))
        filename.close()

def lookupnumtrunclbin(filename,num,truncvalue):
    '''Returns binary value at position num'''
    with open(str(filename), 'rb') as filehandle:
        filehandle.seek((num-1)*(truncvalue+1))
        return filehandle.read(truncvalue)

def lookupelemtrunclbin(filename,elem,truncvalue):
    '''Returns position of elem in binary file'''
    with open(str(filename), 'rb') as filehandle:
        counter = 0
        while True:
            counter+=1
            bytegroup = filehandle.read(int(truncvalue/2))
            if elem[2:2+truncvalue] == bytegroup.hex():
                return counter
            elif bytegroup == b'':
                return None

def lookupelemtrunclfilepartsbin(elem,truncvalue):
    """
    Returns position of elem in 16 truncated file parts.
    Example: 
    lookupelemtrunclfilepartsbin(str(455*PP.g),16)
    """
    result = None
    for i in range(1,17):
        print(i)
        if result == None:
            result = lookupelemtrunclbin("part"+str(i)+".bin",elem,truncvalue)
            if result != None:
                return result + ((i-1)*2**28)

def babygiantsteptruncbin(gx,truncvalue,giantstepsize):
    """
    Returns position of decrypted value from gx using truncation and Shanks.
    Example: babygiantsteptruncbin(Bn.from_decimal("4294968296")*PP.g,16,32)
    """
    i = 1
    gstp = Bn.from_decimal(str(2**giantstepsize))*PP.g
    res = None
    start = time.time()
    while i <= 2**giantstepsize and res == None:
        print(str(i)+"/"+str(2**giantstepsize),end='\r',flush=True)
        res = lookupelemtrunclfilepartsbin(str(gx),truncvalue)
        gx = gx - gstp
        i+=1
    if res == None:
        print("Total time: " + str(round((time.time() - start) ,3)) + str(" sec"))
        return None
    else:
        print("Total time: " + str(round((time.time() - start) ,3)) + str(" sec"))
        return res+(i-2)*(2**giantstepsize)

class Logger(object):
    def __init__(self):
        self.terminal = sys.stdout
        self.log = open("logfile.log", "a")

    def write(self, message):
        self.terminal.write(message)
        self.log.write(message)  

    def flush(self):
        pass    

sys.stdout = Logger()

def varTruncNew(size,startTrunc,endTrunc):
    """
    First part of Algorithm 1.
    """
    #size = 32 for 2**32, 16 for 2**16
    #startTrunc: when to start truncating (in hexes)
    #endTrunc: when to stop truncating (in hexes)
    #create "Gamma" list which stores truncation value for each
    gammalist = [0]*2**(size-12)
    #create table "B1" for the first values (2^20 or 2^4)
    B1 = []

    start = time.time()
    print("**Begin**")
    with open("part1", 'r') as A1:
        for _ in range(0,2**(size-12)):
            B1.append(A1.readline()[:-1])
    T =startTrunc #Truncation factor with no existing collisions (in hexes)
    while (T>=endTrunc):
        print("******************")
        print("Truncation: "+str(T))
        print("Time elapsed: " + str(   round(time.time() - start,2)    ) + " sec"  )
        for i in range(1,17):
            #Open each A1 table
            print("Opening Table " +str(i))
            print("Time elapsed: " + str(   round(time.time() - start,2)    ) + " sec"  )
            with open("part"+str(i), 'r') as A1:
                A2 = set()
                for num, line in enumerate(A1):
                    if (i != 1 or num >= 2**(size-12)):
                        A2.add(line[:T]) #remove also newline char
            for j, elem in enumerate(B1):
                if gammalist[j] == 0:
                    if elem[:T] in A2:
                        gammalist[j] = T
        T = T-1 #increase truncation
    print(gammalist)
    print(Counter(gammalist))

def file2list(fname):
    with open(fname) as f:
        x = [line.rstrip() for line in f]
    return ast.literal_eval(x[0])

def varTruncNewB(size,startTrunc,endTrunc):
    """
    Second part of Algorithm 1 (self check in table B)
    """
    T =startTrunc #Truncation factor with no existing collisions (in hexes)
    B = file2list('gamma.txt')
    print(Counter(B))
    num = 0
    Btlist = []
    with open("part1") as myfile:
        Btlist = [next(myfile) for x in range(2**(size-12))]
    while (T>=endTrunc):
        print(T)
        with open("part1", 'r') as A1:
            Bt = dict()
            for elem in Btlist:
                if elem[:T] in Bt:
                    Bt[elem[:T]] = True
                else:
                    Bt[elem[:T]] = False
        for j, elem in enumerate(Btlist):
            if Bt[elem[:T]] == True and B[j] <T:
                B[j] = T                
        T = T-1 #increase truncation
    print(Counter(B))
