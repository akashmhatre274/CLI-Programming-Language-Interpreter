
### INTERPRETER FOR OBJECT-ORIENTED LANGUAGE

"""The interpreter processes parse trees of this format:

PTREE ::=  [DLIST, CLIST]

DLIST ::=  [ DTREE* ]
           where  DTREE*  means zero or more DTREEs
DTREE ::=  ["int", ID, ETREE]  |  ["proc", ID, ILIST, [], CLIST]
           (note: the [] in the "proc" operator tree will be used in Part B)

CLIST ::=  [ CTREE* ]
CTREE ::=  ["=", LTREE, ETREE]  |  ["if", ETREE, CLIST, CLIST]
        |  ["print", ETREE]  |  ["call", LTREE, ELIST]

ELIST ::=   [ ETREE* ]
ETREE ::=  NUM  |  [OP, ETREE, ETREE] |  ["deref", LTREE]  
      where  OP ::=  "+"  | "-"

LTREE ::=  ID

ILIST ::= [ ID* ]
ID    ::=  a nonempty string of letters

NUM   ::=  a nonempty string of digits


The interpreter computes the meaning of the parse tree, which is
a sequence of updates to heap storage.

You will extend the above to include declarations and calls of parameterized
procedures.
"""


from heapmodule import *   # import the contents of the  heapmodule.py  module 


### INTERPRETER FUNCTIONS, one for each class of parse tree listed above.
#   See the end of program for the driver function,  interpretPTREE


def interpretPTREE(tree) :
    """interprets a complete program tree
       pre: tree is a  PTREE ::= [ DLIST, CLIST ]
       post: heap holds all updates commanded by the  tree
    """
    initializeHeap()
    interpretDLIST(tree[0])
    interpretCLIST(tree[1])
    print("Successful termination.")
    printHeap()


def interpretDLIST(dlist) :
    """pre: dlist  is a list of declarations,  DLIST ::=  [ DTREE+ ]
       post:  memory  holds all the declarations in  dlist
    """
    for dec in dlist :
        interpretDTREE(dec)


def interpretDTREE(d) :
    """pre: d  is a declaration represented as a DTREE:
       DTREE ::=  ["int", ID, ETREE]  |  ["proc", ID, ILIST, [], CLIST] (WRITE ME)
       post:  heap is updated with  d
    """
    ### WRITE ME
    active_ns = activeNS()
    #print("active ns ", active_ns)
    # ["int", ID, ETREE]  |  ["proc", ID, ILIST, [], CLIST]
    # ["int", "x", "2"]  |  ["proc", "p", ['y', 'z'], [], [...]]
    if d[0] == 'int': # d = ["int", ID, ETREE] 
        #var = d[1]
        #val = interpretETREE(d[2])
        #print("print d int: ",d)
        #valLTreeInt = interpretLTREE(d[1])
        #
        # print('valLTreeInt: ', valLTreeInt)
        val = interpretETREE(d[2])
        declare(active_ns, d[1], val)
    # ["proc", ID, ILIST, [], CLIST]
    elif d[0] == 'proc': 
        # closure = {"body": d[4], "params": d[2], "type": d[0], "link":active_ns}
        
        #ansLTree = interpretLTREE(d[1])
        #interpretCLIST(d[4]) 
        #print("LTree val proc: ", ansLTree)

        # proc_name = d[1]
        # param_list = d[2]
        # cmd_list = d[4]
        #print("print d: ",d)
        handle = allocateNS() # heap[handle] = {} heap = {"h0":{...}, "h1":{}}
        declare(active_ns, d[1], handle) # heap = {active_ns: {..., proc_name:handle, ...}}
        heap[handle]['type'] = d[0]
        heap[handle]['params'] = d[2]
        heap[handle]['local'] = d[3]
        heap[handle]['body'] = d[4]
        heap[handle]['link'] = active_ns
        #print("d[3]", d[3])
        #handle = allocateNS()
    elif d[0] == 'ob':
        val = interpretETREE(d[2])
        declare(active_ns, d[1], val) 
    elif d[0] == 'class':
        handle = allocateNS() # heap[handle] = {} heap = {"h0":{...}, "h1":{}}
        declare(active_ns, d[1], handle) # heap = {active_ns: {..., proc_name:handle, ...}}
        heap[handle]['type'] = d[0]
        heap[handle]['body'] = d[2]
        heap[handle]['link'] = active_ns
        #interpretTTREE(d[2])
    #elif d[0] == 'override':
        #print('override:',d)

        
          
    


def interpretCLIST(clist) :
    """pre: clist  is a list of commands,  CLIST ::=  [ CTREE+ ]
                  where  CTREE+  means  one or more CTREEs
       post:  memory  holds all the updates commanded by program  p
    """
    for command in clist :
        interpretCTREE(command)


def interpretCTREE(c) :
    """pre: c  is a command represented as a CTREE:
       CTREE ::=  (WRITE ME) ["=", LTREE, ETREE]  |  ["if", ETREE, CLIST, CLIST]
        |  ["print", ETREE]  |  ["call", LTREE, ELIST]
       post:  heap  holds the updates commanded by  c
    """
    operator = c[0]
    if operator == "=" :   # , ["=", LTREE, ETREE]
        #print('c:', c)
        handle, field = interpretLTREE(c[1])  # returns (handle,field) pair
        rval = interpretETREE(c[2])
        update(handle, field, rval)
    elif operator == "print" :   # ["print", LTREE]
        print(interpretETREE(c[1]))
        printHeap()
    elif operator == "if" :   # ["if", ETREE, CLIST1, CLIST2]
        test = interpretETREE(c[1])
        if test != 0 :
            interpretCLIST(c[2])
        else :
            interpretCLIST(c[3]) 
    # WRITE ME 
    # interpret ["call", LTREE, ELIST] # ["call", "p", ['1', '2']] if proc p(x, y):...
    elif operator == "call":
        params_list = []
        parent_ns = ''
        cmd_list =[]
        local_dec = []
        #global parent_ns, cmd_list, params_list
        # step(i) Compute the meaning of L, verify that the meaning is the handle to a procedure closure, 
        # and extract from that closure these parts: IL, CL, and parentns link. 
        # (If L is not bound to a handle of a proc closure, it's an error that stops execution.) 
        #print(c[1])
        # Compute the meaning of L, find the closure handle if L is procedure 
        
        current_ns, proc_name = interpretLTREE(c[1])
        closure_handle = lookup(current_ns, proc_name)
        # verify that the closure_handle meaning is the handle to a procedure closure
        if isinstance(closure_handle, int):
            crash("we can't call a interger")

        # valid closure handle, then extract IL, CL, parentns link
        if isinstance(closure_handle, str):
            # extract parameters
            params_list = lookup(closure_handle, "params")
            # extract procedure commands (body)
            cmd_list = lookup(closure_handle, "body")
            # extract link, where this procedure is defined
            parent_ns = lookup(closure_handle, "link")
            local_dec = lookup(closure_handle, "local")
            #print("parent_ns",parent_ns)
            #print("param_list",params_list)
            #print("cmd_list",cmd_list)
        else:
            crash(heap,"crash new")
        # step (ii) evaluate EL to a list of values 
        # print("parent_ns",parent_ns)
        # print("param_list",params_list)
        # print("cmd_list",cmd_list)
        params_vals = []
        for etree in c[2]:
            val = interpretETREE(etree)
            params_vals.append(val)

        # step (iii) Allocate a new namespace. 
        new_ns = allocateNS()

        # step (iv) Within the new namespace, bind parentns to the handle extracted from the closure; 
        # bind the values from EL to the corresponding names in IL. (Make certain that the number of arguments in EL equals the number of parameters in IL. Otherwise, it's an error that prints a message and stops execution).

        # Within the new namespace, bind parentns to the handle extracted from the closure; 
        heap[new_ns]["parentns"] = parent_ns 

        # bind the values from EL to the corresponding names in IL. (Make certain that the number of arguments in EL equals the number of parameters in IL. Otherwise, it's an error that prints a message and stops execution).
        if len(params_list) != len(params_vals):
            crash(heap,"parameters don't match the definition")
        else:
            for param, val in zip(params_list, params_vals):
                heap[new_ns][param] = val

        #  step (v) Push the new namespace's handle onto the activation stack, execute CL, and upon completion pop the activation stack.
        pushHandle(new_ns)

        # execute CL,
        
        interpretDLIST(local_dec)
        interpretCLIST(cmd_list)
        #print(heap)

        # pop the activation stack.
        popHandle()

        # not requred, del the new name space
        #del heap[new_ns]

    else :  crash(c, "invalid command")

def interpretTTREE(ttree):
    global activationStack
    active_ns = activeNS()
    ans = ''
    if ttree[0] == 'struct':
        
        # handle = allocateNS()
        # heap[handle]['parentns'] = active_ns
        handle = allocateNS()
        #print("ht",handle)
        heap[handle]['parentns'] = active_ns
        #active_ns = activeNS()
        #print("handle",handle)
        #print("activation stack at ttree: ",activationStack)
        #print("active ns ttree:", active_ns)
        pushHandle(handle)
        interpretDLIST(ttree[1])
        popHandle()
        ans = handle

        #declare(active_ns,ttree[1], topHandle())
        #return handle
    elif ttree[0] == 'call':
        ansLT = interpretLTREE(ttree[1])
        handle = lookup(ansLT[0], ansLT[1])
        #print("ans outside if",anslookup)
        #print('active ns in Call ttree', active_ns)
        if lookup(handle,'type') == 'class':
            body = lookup(handle,'body')
            #print("ans[0]",ans[0])
            pushHandle(ansLT[0])
            ans = interpretTTREE(body)
            popHandle()
            update(ans,'parentns', active_ns)

        #print("ttree ans:",ans)
    # elif ttree[0] == 'extend':
    #     #print('extend:',ttree)
    #     interpretTTREE(ttree[1])
    #     interpretDLIST(ttree[2])
    else:
        crash('Error ttree', ttree)
    return ans

def interpretETREE(etree) :
    """interpretETREE computes the meaning of an expression operator tree.
         ETREE ::=  NUM  |  [OP, ETREE, ETREE] |  ["deref", LTREE] 
         OP ::= "+" | "-"
        post: updates the heap as needed and returns the  etree's value
    """
    ans = 0
    #active_ns = activeNS()
    #print("Etree:", etree)
    if isinstance(etree, str) and etree.isdigit() :  # NUM  -- string of digits
      ans = int(etree) 
    elif  etree[0] in ("+", "-") :    # [OP, ETREE, ETREE]
        ans1 = interpretETREE(etree[1])
        ans2 = interpretETREE(etree[2])
        if isinstance(ans1,int) and isinstance(ans2, int) :
            if etree[0] == "+" :
                ans = ans1 + ans2
            elif etree[0] == "-" :
                ans = ans1 - ans2
        else : crash(etree, "addition error --- nonint value used")
    elif  etree[0] == "deref" :    # ["deref", LTREE]
        handle, field = interpretLTREE(etree[1])
        ans = lookup(handle,field)
    elif etree == "nil":
        ans = 'nil'
    elif etree[0] == "new":
        ans = interpretTTREE(etree[1])
    else :  crash(etree, "invalid expression form")
    return ans


def interpretLTREE(ltree) :
    """interpretLTREE computes the meaning of a lefthandside operator tree.
          LTREE ::=  ID
       post: returns a pair,  (handle,varname),  the L-value of  ltree
    """

    ans = []
    active_ns = activeNS()
    #print("active ns:", active_ns)
    
    # WRITE ME: MODIFY THE FUCNTION 
    if isinstance(ltree, str) and  ltree[0].isalpha()  :  #  ID 
     # if ltree is a valid variable name, then we need to check whether this ltree 
     # can be found or not in the current active namespace
     # find the current active namespace
        
        #print("ltree",ltree)
        #print('active ns', active_ns)
        #print('heap active ns:', heap[active_ns])
        if ltree in heap[active_ns]:
            ans = [active_ns, ltree] 
        else:
        # then check whether ltree in heap[active_ns] or not
         #if ltree not in heap[active_ns], then parent_ns = heap[active_ns]["parentns"], check whether ltree is in heap[parent_ns] or not
          # use the handle to the active namespace

            parent_ns = heap[active_ns]["parentns"]
        
            while parent_ns != 'nil':
                #print("parent_ns", parent_ns)
                if ltree in heap[parent_ns]:
                    ans = [parent_ns, ltree] 
                    break   
                parent_ns = heap[parent_ns]["parentns"]
        #print("ams:", ans)
        

    #else :
    elif isinstance(ltree, list) and ltree[0] == "dot" :
        #crash(ltree, "illegal L-value")
        handle, ltreeval = interpretLTREE(ltree[1])
        #print("handel:", handle)
        #print("lval", ltreeval)
        handle = lookup(handle, ltreeval)
        ans = (handle, ltree[2])
    else:
        crash(ltree, "illegal L-value")
        
    return ans


def crash(tree, message) :
    """pre: tree is a parse tree,  and  message is a string
       post: tree and message are printed and interpreter stopped
    """
    print("Error evaluating tree:", tree)
    print(message)
    print("Crash!")
    printHeap()
    #raise Exception   # stops the interpreter




