----------------------------- MODULE VectorClocks -----------------------------
EXTENDS Integers, TLC, Sequences
CONSTANTS Procs, MAX

(*
--algorithm VectorClocks
variables
  msgs = [p \in Procs |-> [q \in Procs |-> 0]]; \* defined as Vector Clock 
    
define
  \* returns the maximum value for each element of two vectors
  Max(v1, v2) == [p \in Procs |-> IF v1[p] > v2[p] THEN v1[p] ELSE v2[p]]
end define;

fair process VectorClock \in Procs
variables
  vc = [p \in Procs |-> 0] \* Initially all clocks are zero
begin Main:
  while vc[self] < MAX do
    either Internal: \* increments local clock 
      vc[self] := vc[self] + 1;
    or Send: \* increments local clock and sends it to another process
      vc[self] := vc[self] + 1;
      with p \in Procs \ {self} do \* send vc to 'p' via msgs[p] 
        msgs[p] := vc;
      end with;
    or Receive: \* increments local clock and calcs maximum of two clocks
      vc := Max(vc, msgs[self]);
      goto Internal; \*vc[self] := vc[self] + 1;
    end either;
  end while;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION
VARIABLES msgs, pc

(* define statement *)
Max(v1, v2) == [p \in Procs |-> IF v1[p] > v2[p] THEN v1[p] ELSE v2[p]]

VARIABLE vc

vars == << msgs, pc, vc >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ msgs = [p \in Procs |-> [q \in Procs |-> 0]]
        (* Process VectorClock *)
        /\ vc = [self \in Procs |-> [p \in Procs |-> 0]]
        /\ pc = [self \in ProcSet |-> "Main"]

Main(self) == /\ pc[self] = "Main"
              /\ IF vc[self][self] < MAX
                    THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "Internal"]
                            \/ /\ pc' = [pc EXCEPT ![self] = "Send"]
                            \/ /\ pc' = [pc EXCEPT ![self] = "Receive"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << msgs, vc >>

Internal(self) == /\ pc[self] = "Internal"
                  /\ vc' = [vc EXCEPT ![self][self] = vc[self][self] + 1]
                  /\ pc' = [pc EXCEPT ![self] = "Main"]
                  /\ msgs' = msgs

Send(self) == /\ pc[self] = "Send"
              /\ vc' = [vc EXCEPT ![self][self] = vc[self][self] + 1]
              /\ \E p \in Procs \ {self}:
                   msgs' = [msgs EXCEPT ![p] = vc'[self]]
              /\ pc' = [pc EXCEPT ![self] = "Main"]

Receive(self) == /\ pc[self] = "Receive"
                 /\ vc' = [vc EXCEPT ![self] = Max(vc[self], msgs[self])]
                 /\ pc' = [pc EXCEPT ![self] = "Internal"]
                 /\ msgs' = msgs

VectorClock(self) == Main(self) \/ Internal(self) \/ Send(self)
                        \/ Receive(self)

Next == (\E self \in Procs: VectorClock(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(VectorClock(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Invariants
VectorClockOK == (\A k,l \in Procs: vc[k][k] >= vc[l][k])

===============================================================================
\* Modification History
\* Last modified Sun Nov 25 21:39:03 PST 2018 by ocosta
\* Created Sat Nov 17 15:07:39 PST 2018 by ocosta
