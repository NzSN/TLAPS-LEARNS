
----------------------- MODULE SimpleMutex ----------------------
EXTENDS Integers 

(***** --algorithm SimpleMutex {  
    variables flag = [i \in {0, 1} |-> FALSE] ; 
    process (proc \in {0,1}) {  
        s1: while (TRUE) {  flag[self] := TRUE ; 
        s2: await flag[1-self] = FALSE ; 
        cs: skip ; 
        s3: flag[self] := FALSE } } } 
*****) 
\* BEGIN TRANSLATION (chksum(pcal) = "fb83c34" /\ chksum(tla) = "718dc121")
VARIABLES flag, pc

vars == << flag, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "s2"]

s2(self) == /\ pc[self] = "s2"
            /\ flag[1-self] = FALSE
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ flag' = flag

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ flag' = flag

s3(self) == /\ pc[self] = "s3"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "s1"]

proc(self) == s1(self) \/ s2(self) \/ cs(self) \/ s3(self)

Next == (\E self \in {0,1}: proc(self))

Mutex == ~(pc[0] = "cs") /\ (pc[1] = "cs")
Spec == Init /\ [][Next]_vars

TypeOK == /\ flag \in [{0, 1} -> BOOLEAN]
          /\ pc \in [{0, 1} -> {"s1", "s2", "cs", "s3"}]
Inv == /\ TypeOK
       /\ \A i \in {0,1} :
        /\ (flag[i] = TRUE) <=> (pc[i] \in {"s2", "cs", "s3"})
        /\ (pc[i] = "cs") => (flag[1-i] = FALSE) \/ (pc[1-i] = "s2")

THEOREM Spec => []Mutex
<1>0. Init => Inv
  <2>0. SUFFICES ASSUME Init
                 PROVE  Inv
    OBVIOUS
  <2>1. TypeOK
    BY DEF Init, Inv, TypeOK
  <2>2. \A i \in {0,1} : 
        /\ (flag[i] = TRUE) <=> (pc[i] \in {"s2", "cs", "s3"})
        /\ (pc[i] = "cs") => (flag[1-i] = FALSE) \/ (pc[1-i] = "s2")
    <3>0 SUFFICES ASSUME NEW i \in {0,1}
                  PROVE  /\ (flag[i] = TRUE) <=> (pc[i] \in {"s2", "cs", "s3"})
                         /\ (pc[i] = "cs") => (flag[1-i] = FALSE) \/ (pc[1-i] = "s2")
        OBVIOUS
        <3>1. 
        
  <2>3. QED
    BY <2>1, <2>2 DEF Inv
<1>1. Inv /\ [Next]_vars => Inv'
<1>2. QED
\* END TRANSLATION 

===================================================================
