from collections import defaultdict
from copy import deepcopy
import time

file_input = open('input.txt','r')

def implicationConvert(line):
	#find index of implication sign
	index = line.find("=>")
	leftPcount = 0
	rightPcount = 0
	leftPindex = 0

	#find number of ) immedately left of sign
	for x in range(index-1,-1,-1):
		if line[x] != ")":
			break
		rightPcount += 1

	#if only one ) then there is only one literal
	if rightPcount == 1:
		tempindex = line.rfind("(", 0, index)
		for x in range(tempindex-1,-1,-1):
			if not (line[x].isalpha()):
				leftPindex = (x+1)
				break
	#find the left most ( that completes the clause
	else:
		for x in range(index-rightPcount-1, -1, -1):
			if line[x] == ")":
				leftPcount -= 1
			if line[x] == "(":
				leftPcount += 1
			if leftPcount == rightPcount:
				leftPindex = x
				break

	negationClause = line[leftPindex:index]
	#finding that 'P' is in P => Q, create the ~P v Q
	newline = (line[0:leftPindex]+"(~"+line[leftPindex:index]+")|"+line[index+2:])

	return newline

def negationInward(line):
	#evaluate (~(P))
	#find the first ~( bc that needs to be distributed
	index = line.find("~(")
	leftPcount = 1
	rightPindex = 0

	#find the right ) of clause that completes the ~(P)
	for x in range((index+2),len(line),1):
		if line[x] == "(":
			leftPcount += 1
		if line[x] == ")":
			leftPcount -= 1
		if leftPcount == 0:
			rightPindex = x
			break

	#get just the (P)
	partialString = line[(index+1):(rightPindex+1)]

	#if P is ~X making the case (~(~X))
	if partialString[1] == "~":
		#get just X
		partialString = partialString[2:(len(partialString)-1)]
		return (line[0:(index-1)]+partialString+line[(rightPindex+2):len(line)])

	newline = ""
	newline += (line[0:(index-1)]+"((~")

	Rindex = 0
	pcount = 1
	operatorIndex = 0
	#left part of clause is a clause
	if partialString[1] == "(":
		for x in range(2,len(partialString),1):
			if partialString[x] == "(":
				pcount += 1
			if partialString[x] == ")":
				pcount -= 1
			if pcount == 0:
				Rindex = x
				break
		newline += partialString[1:(Rindex+1)]
		operatorIndex = (Rindex+1)
	else:
		for x in range(0,len(partialString),1):
			if (partialString[x] == "&" or partialString[x] == "|"):
				operatorIndex = x
				break
		newline += partialString[1:operatorIndex]

	if partialString[operatorIndex] == "&":
		newline += ")|"
	else:
		newline += ")&"

	newline += "(~"
	newline += partialString[(operatorIndex+1):]
	newline += ")"
	newline += line[(rightPindex+2):]

	return newline

def andRemove(line):
	leftPcount = 1
	splitList = []
	operatorIndex = 0
	if line[1] == "(":
		for x in range(2,len(line),1):
			if line[x] == "(":
				leftPcount += 1
			if line[x] == ")":
				leftPcount -= 1
			if leftPcount == 0:
				operatorIndex = (x+1)
				break
	else:
		for x in range(0,len(line),1):
			if (line[x] == "&" or line[x] == "|"):
				operatorIndex = x
				break

	#if and is the most outer operator just split and return
	if line[operatorIndex] == "&":
		splitList.append(line[1:operatorIndex])
		splitList.append(line[(operatorIndex+1):(len(line)-1)])
		return splitList
	#else separate the two clauses and recursively find &
	else:
		clause = line
		subClause = ""
		leftOperand = ""
		rightOperand = ""
		startIndex = 0
		endIndex = len(line)
		leftAnd = True
		while clause[operatorIndex] != "&":
			#(PvQ)
			previousOperatorIndex = operatorIndex
			previousClause = clause
			leftOperand = clause[1:operatorIndex]
			rightOperand = clause[(operatorIndex+1):(len(clause)-1)]
			#in first part of clause
			if "&" in leftOperand:
				subClause = rightOperand
				clause = leftOperand
				leftAnd = True
			else:
				subClause = leftOperand
				clause = rightOperand
				leftAnd = False

			leftPcount = 1
			if clause[1] == "(":
				for x in range(2,len(clause),1):
					if clause[x] == "(":
						leftPcount += 1
					if clause[x] == ")":
						leftPcount -= 1
					if leftPcount == 0:
						operatorIndex = (x+1)
						break
			else:
				for x in range(0,len(clause),1):
					if (clause[x] == "&" or clause[x] == "|"):
						operatorIndex = x
						break
			if clause[operatorIndex] == "|":
				if leftAnd == True:
					endIndex -= (len(previousClause)-previousOperatorIndex)
					startIndex += 1
				else:
					startIndex += (previousOperatorIndex+1)
					endIndex -= 1
		leftOperand = clause[1:operatorIndex]
		rightOperand = clause[(operatorIndex+1):(len(clause)-1)]
		newline = ""
		newline += line[0:startIndex]
		newline += ("(("+leftOperand+"|"+subClause+")&("+rightOperand+"|"+subClause+"))")
		newline += line[endIndex:]
		splitList.append(newline)
		return splitList

def nameOfLiterals(line):
	nameList = []
	
	
	literalIndex = 0
	argStartIndex = 0
	argEndIndex = 0
	while "(" in line[1:]:
		pIndex = line.find("(", 1, len(line))
		predicate = ""
		negation = False
		argument = []
		if line[(pIndex-1)].isalpha():
			#loop till endof predicate name
			for x in range((pIndex-1),-1,-1):
				if line[x].isalpha():
					literalIndex = x
				else:
					break
			predicate = line[literalIndex:pIndex]
			if literalIndex == 0:
				negation = False
			elif line[(literalIndex-1)] == "~":
				negation = True
			else:
				negation = False
			argStartIndex = (pIndex+1)
			for x in range((pIndex+1),len(line),1):
				if line[x].isalpha():
					argEndIndex = x
				elif line[x] == ",":
					argument.append(line[argStartIndex:x])
					argStartIndex = (x+1)
				else:
					break
			argument.append(line[argStartIndex:(argEndIndex+1)])


			nameList.append((predicate,negation,argument))
		line = line[(pIndex+1):]
	return nameList


def sentenceParse(line):
	while ("=>" in line):
		line = implicationConvert(line)
	while ("~(" in line):
		line = negationInward(line)
	needSplit = []
	doneSplit = []
	if "&" in line:
		needSplit.append(line)
	else:
		doneSplit.append(line)
	while (len(needSplit) > 0):
		returnedList = andRemove(needSplit.pop())
		for x in returnedList:
			if "&" in x:
				needSplit.append(x)
			else:
				doneSplit.append(x)
	return doneSplit

#inputs
Qnum = int(file_input.readline().rstrip())
queries = []
for x in range(Qnum):
	line = file_input.readline().rstrip()
	line = line.replace(" ","")
	(a,b,c) = nameOfLiterals(line)[0]
	result = []
	#negate the queries here, since we need to anyways
	if b == True:
		result.append((a,False,c))
	else:
		result.append((a,True,c))
	queries.append(result)
Snum = int(file_input.readline().rstrip())
sentences = defaultdict(list)
for w in range(Snum):
	line = file_input.readline().rstrip()
	line = line.replace(" ","")
	
	#parse the input
	#change implication to CNF, separate AND
	inputList = sentenceParse(line)
	for x in inputList:
		nameList = nameOfLiterals(x)
		for y in nameList:
			if not(nameList in sentences[y[0]]):
				sentences[y[0]].append(nameList)

file_input.close()
file_output = open('output.txt','w')
#loop through query and solve
for x in queries:
	start = time.time()
	#for each new query we refresh the ongoingQ, KB, then we add the query to KB
	ongoingQ = []
	ongoingQ.append(x)
	KB = defaultdict(list)
	KB = deepcopy(sentences)
	KB[(x[0][0])].append(x)


	#check all the queries that resulted from evaluation
	while ongoingQ:
		current = ongoingQ.pop(0)
		#tempsearchList  = []
		searchList = []
		#get all sentences that has at least one of the predicates
		for eachPred in current:
			resultKB = KB[eachPred[0]]
			for element in resultKB:
				if not(element in searchList):
					searchList.append(element)
		'''
		#loop through the list of sentences and keep only one that has all the predicates
		for eachSentence in tempsearchList:
			addSentence = True
			for element in current:
				hasPredicate = False
				for eachPred in eachSentence:
					if element[0] == eachPred[0]:
						hasPredicate = True
				if hasPredicate == False:
					addSentence = False
			if addSentence == True:
				searchList.append(eachSentence)
		'''



		goodList = defaultdict(list)
		#go through the sentences that have the same name inside
		for eachSentence in searchList:
			needAdd = False
			keyAdd = ""
			needSkip = False
			for element in current:
				for eachPred in eachSentence:
					#add ones that can be negated
					if (eachPred[0] == element[0]) & (eachPred[1] != element[1]):
						needAdd = True
						needSkip = True
						keyAdd = element[0]
						for argIndex in range(len(eachPred[2])):
							if eachPred[2][argIndex][0].isupper() & element[2][argIndex][0].isupper() & (eachPred[2][argIndex] != element[2][argIndex]):
								needAdd = False
								break
					if needSkip:
						break
				if needSkip:
					break
			if needAdd:
				goodList[keyAdd].append(eachSentence)


		if len(ongoingQ) == 0 & len(goodList)  == 0:
			print "False"
			break


		#if current is just one predicate
		#go through all the sentences that can be negated
		if len(current) == 1:
			finished = False
			checkList = goodList[(current[0][0])]
			for eachSentence in checkList:
				#this means no OR, just predicate, so contradiction
				if len(eachSentence) == 1:
					needSkip = False
					for argIndex in range(len(eachSentence[0][2])):
						if (eachSentence[0][2][argIndex].isupper()) & (current[0][2][argIndex].isupper()) & (eachSentence[0][2][argIndex] != current[0][2][argIndex]):
							needSkip = True
							break
					if needSkip:
						break
					else:
						file_output.write("TRUE\n")
						finished = True
						break
				else:
					temppredicate = ()
					argumentList = []
					#find the differences between current and predicate
					for predicate in eachSentence:
						if (predicate[0] == current[0][0]) & (predicate[1] != current[0][1]):
							temppredicate = predicate
							for argIndex in range(len(predicate[2])):
								if current[0][2][argIndex][0].isupper():
									argumentList.append(current[0][2][argIndex])
								else:
									argumentList.append(predicate[2][argIndex])
							break

					#unify for current
					'''
					if current[0][2] != argumentList:
						newArg = []
						for argIndex in range(len(argumentList)):
							if argumentList[argIndex][0].isupper():
								newArg.append(argumentList[argIndex])
							else:
								newArg.append(current[0][2][argIndex])
						newCurrent = [(current[0][0],current[0][1],newArg)]
						KB[current[0][0]].append(newCurrent)
						ongoingQ.append(newCurrent)
					'''
					#unify for sentence
					tempSentence = deepcopy(eachSentence)
					if temppredicate[2] != argumentList:
						newSentence = []
						varNeedChange = dict()
						for argIndex in range(len(temppredicate[2])):
							if (temppredicate[2][argIndex] != argumentList[argIndex]):
								varNeedChange[temppredicate[2][argIndex]] = argumentList[argIndex]
						tempSentence.remove(temppredicate)
						for eachPred in tempSentence:
							newArg = []
							for argIndex in range(len(eachPred[2])):
								if eachPred[2][argIndex] in varNeedChange:
									newArg.append(varNeedChange[eachPred[2][argIndex]])
								else:
									newArg.append(eachPred[2][argIndex])
							newSentence.append((eachPred[0],eachPred[1],newArg))
						for eachpred in newSentence:
							KB[eachPred[0]].append(newSentence)
						ongoingQ.append(newSentence)

					else:
						tempSentence.remove(temppredicate)
						ongoingQ.append(tempSentence)
						for eachpred in tempSentence:
							KB[eachPred[0]].append(tempSentence)

			if finished:
				break

		#length of current is more than one predicate
		else:
			for eachKey in goodList:
				currList = goodList[eachKey]
				for sentence in currList:
					if len(sentence) == 1:
						temppredicate = ()
						argumentList = []
						#find the differences between 
						for predicate in current:
							if (predicate[0] == sentence[0][0]) & (predicate[1] != sentence[0][1]):
								temppredicate = predicate
								for argIndex in range(len(predicate[2])):
									if sentence[0][2][argIndex][0].isupper():
										argumentList.append(sentence[0][2][argIndex])
									else:
										argumentList.append(predicate[2][argIndex])
								break

						'''
						#unify for sentence
						if sentence[0][2] != argumentList:
							newArg = []
							for argIndex in range(len(argumentList)):
								if argumentList[argIndex][0].isupper():
									newArg.append(argumentList[argIndex])
								else:
									newArg.append(sentence[0][2][argIndex])
							newSentence = [(sentence[0][0],sentence[0][1],newArg)]
							KB[sentence[0][0]].append(newSentence)
							ongoingQ.append(newSentence)
						'''
						#unify for current
						tempCurrent = deepcopy(current)
						if temppredicate[2] != argumentList:
							newCurrent = []
							varNeedChange = dict()
							for argIndex in range(len(temppredicate[2])):
								if (temppredicate[2][argIndex] != argumentList[argIndex]):
									varNeedChange[temppredicate[2][argIndex]] = argumentList[argIndex]
							tempCurrent.remove(temppredicate)
							for eachPred in tempCurrent:
								newArg = []
								for argIndex in range(len(eachPred[2])):
									if eachPred[2][argIndex] in varNeedChange:
										newArg.append(varNeedChange[eachPred[2][argIndex]])
									else:
										newArg.append(eachPred[2][argIndex])
								newCurrent.append((eachPred[0],eachPred[1],newArg))
							for eachpred in newCurrent:
								KB[eachPred[0]].append(newCurrent)
							ongoingQ.append(newCurrent)
						else:
							tempCurrent.remove(temppredicate)
							ongoingQ.append(tempCurrent)
							for eachPred in tempCurrent:
								KB[eachPred[0]].append(tempCurrent)
					#length of sentence is more than 1, so both current and sentence more than 1
					else:
						oppositeSent = []
						oppositeCurr = []
						argumentList = defaultdict(list)

						#find the differences between current and predicate
						needSkip = False
						for predicate in sentence:
							for eachPred in current:
								if (predicate[0] == eachPred[0]) & (predicate[1] != eachPred[1]):
									oppositeSent.append(predicate)
									oppositeCurr.append(eachPred)
									for argIndex in range(len(predicate[2])):
										if predicate[2][argIndex][0].isupper() & eachPred[2][argIndex][0].isupper() & (predicate[2][argIndex] != eachPred[2][argIndex]):
											needSkip = True
											break
										if eachPred[2][argIndex][0].isupper():
											argumentList[predicate[0]].append(eachPred[2][argIndex])
										else:
											argumentList[predicate[0]].append(predicate[2][argIndex])
									break
								if needSkip:
									break
							if needSkip:
								break
						if needSkip:
							continue


						#combinging sentence
						#var need change in curr
						currNeedChange = dict()
						tempcurrDup = []
						for element in oppositeCurr:
							temp = argumentList[element[0]]
							for argIndex in range(len(element[2])):
								if element[2][argIndex] != temp[argIndex]:
									currNeedChange[element[2][argIndex]] = temp[argIndex]
									tempcurrDup.append(temp[argIndex])
						currDup = []
						for stuff in tempcurrDup:
							if not(stuff in currNeedChange):
								currDup.append(stuff)
						#unify current
						tempCurrent = []
						for predicate in current:
							newArg = []
							for argIndex in range(len(predicate[2])):
								if predicate[2][argIndex] in currDup:
									newArg.append(predicate[2][argIndex]+predicate[2][argIndex])
								elif predicate[2][argIndex] in currNeedChange:
									newArg.append(currNeedChange[predicate[2][argIndex]])
								else:
									newArg.append(predicate[2][argIndex])
							tempCurrent.append((predicate[0],predicate[1],newArg))

						#remove the duplicate ones
						newCurrent = []
						for predicate in tempCurrent:
							skip = False
							for eachPred in oppositeCurr:
								if (predicate[0] == eachPred[0]) & (predicate[1] == eachPred[1]):
									skip = True
									break
							if not(skip):
								newCurrent.append(predicate)


						#var need change in sentence
						sentNeedChange = dict()
						tempsentDup = []
						for element in oppositeSent:
							temp = argumentList[element[0]]
							for argIndex in range(len(element[2])):
								if element[2][argIndex] != temp[argIndex]:
									sentNeedChange[element[2][argIndex]] = temp[argIndex]
									tempsentDup.append(temp[argIndex])

						sentDup = []
						for stuff in tempsentDup:
							if not(stuff in sentNeedChange):
								sentDup.append(stuff)
						#unify current
						tempSentence = []
						for predicate in sentence:
							newArg = []
							for argIndex in range(len(predicate[2])):
								if predicate[2][argIndex] in sentDup:
									newArg.append(predicate[2][argIndex]+predicate[2][argIndex])
								elif predicate[2][argIndex] in sentNeedChange:
									newArg.append(sentNeedChange[predicate[2][argIndex]])
								else:
									newArg.append(predicate[2][argIndex])
							tempSentence.append((predicate[0],predicate[1],newArg))

						#remove the duplicate ones
						newSentence = []
						for predicate in tempSentence:
							skip = False
							for eachPred in oppositeSent:
								if (predicate[0] == eachPred[0]) & (predicate[1] == eachPred[1]):
									skip = True
									break
							if not(skip):
								newSentence.append(predicate)


						#find any with same negation
						sameList = []
						anotherArgList = defaultdict(list)
						needSkip = False
						for predicate in newSentence:
							for eachPred in newCurrent:
								if (predicate[0] == eachPred[0]) & (predicate[1] == eachPred[1]):
									sameList.append((predicate[0],predicate[1]))
									for argIndex in range(len(predicate[2])):
										if predicate[2][argIndex][0].isupper() & eachPred[2][argIndex][0].isupper() & (predicate[2][argIndex] != eachPred[2][argIndex]):
											needSkip = True
											break
										if eachPred[2][argIndex][0].isupper():
											anotherArgList[predicate[0]].append(eachPred[2][argIndex])
										else:
											anotherArgList[predicate[0]].append(predicate[2][argIndex])
									break
								if needSkip:
									break
							if needSkip:
								break
						if needSkip:
							continue

						anotherSent = []
						for predicate in newSentence:
							if not((predicate[0],predicate[1]) in sameList):
								anotherSent.append(predicate)
						anotherCurr = []
						for predicate in newCurrent:
							if ((predicate[0],predicate[1]) in sameList):
								anotherCurr.append((predicate[0],predicate[1],anotherArgList[predicate[0]]))
							else:
								anotherCurr.append(predicate)

						combineSentence = []
						for predicate in anotherSent:
							combineSentence.append(predicate)
						for predicate in anotherCurr:
							combineSentence.append(predicate)
						for predicate in combineSentence:
							KB[predicate[0]].append(combineSentence)
						ongoingQ.append(combineSentence)





		end = time.time()
		diff = int(end-start)
		if diff > 20:
			file_output.write("FALSE\n")
			break
file_output.close()








