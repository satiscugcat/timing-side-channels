Inductive PartialOrder {A: Type} (rel: A -> A -> Type) : Type:= 
| PartialOrderConstructor (rel: A -> A -> Prop) (rel_refl: forall (a: A), rel a a) (rel_trans: forall (a b c: A), rel a b -> rel a c -> rel a c) (rel_antisym: forall (a b: A), (a = b -> False) -> rel a b -> rel b a -> False).

Inductive Join {A: Type} (rel: A -> A -> Type) : A -> A -> A -> Type :=
| JoinConstructor (pOrderProof: PartialOrder rel) (a b join: A) (pleft: rel a join) (pright : rel b join) (pleast: forall ub, rel a ub -> rel b ub -> rel join ub): Join rel a b join
.
Inductive EX {A: Type} (P: A -> Type) : Type :=
| EX_intro (x: A) : P x -> EX  P.

Inductive FALSE :=.
Inductive JoinSemilattice {A: Type} (rel: A -> A -> Type): Type:=
| JoinSemilatticeConstructor (OrdProof: PartialOrder rel)
    (JoinProof: forall (a b: A), EX (fun (join: A) => Join rel a b join)) .

Inductive Var: Type :=
| VarConstructor (n: nat).

Inductive Level: Type :=
| LevelConstructor (n: nat).

Definition level_eq_dec: forall (a b: Level), {a = b} + {a <> b}.
Proof.
  decide equality; decide equality.
Qed.

Definition var_eq_dec: forall (a b: Var), {a = b} + {a <> b}.
Proof.
  decide equality; decide equality.
Qed.

Inductive BinOp:= | Plus | Minus | Add | Divide | And | Or.

Definition total_map (A: Type) := Var -> A.

Definition t_empty {A: Type} (v: A) : total_map A := (fun _ => v).

Definition t_update {A: Type} (m: total_map A) (x: Var) (v: A) := fun x' => if var_eq_dec x x' then v else m x'.



Inductive Primitive :=
| TruePrimitive
| FalsePrimitive
| NatPrimitive (n: nat).

Definition prim_eq_dec: forall (a b: Primitive), {a=b} + { a <> b}.
Proof.
  repeat (decide equality).
Qed.

Definition MemStore := Var -> Primitive * Level.
(* Definition MemEmpty := t_empty UndefStoreValue. *)
Definition MemUpdate (mu: MemStore) (x: Var) (p: Primitive) (k: Level) := t_update mu x (p, k).

Inductive Expression :=
| PrimitiveExpression (prim: Primitive) (k: Level)
| VarExpression (x: Var)
| CommaExpression (e1 e2: Expression)
| BinOpExpression (binop: BinOp) (e1 e2: Expression).

Inductive Command : Type :=
| SkipCommand
| AssnCommand (x: Var) (e: Expression)
| SeqCommand (c1 c2: Command)
| IfCommand (e: Expression) (c1 c2: Command)
| WhileCommand (e: Expression) (c: Command)

with DebranchCommand : Type:=
| Debranch (c: Command) (n: bool) (l: Level).

Definition PrimToBool (n: Primitive) : bool := match n with | TruePrimitive => true | _ => false end.

Inductive Timing :=
| CONST
| VAR
| OPER (oper: BinOp)
| COMMA
| SKIP
| SEQ
| WHILEF
| ASSN
| IF_HIGH
| IF_LOW
| WHILET

| DEB_SKIP
| DEB_ASSN
| DEB_SEQ
| DEB_IF_HIGH
| DEB_IF_LOW
| DEB_WHILET
| DEB_WHILEF.
Definition timing_eq_dec: forall (a b: Timing), {a=b} + {a<>b}.
Proof.
  decide equality; decide equality.
Qed.

Definition TimingMap := Timing -> nat.

Definition SingleTiming (t: Timing): TimingMap := fun t' =>
  if timing_eq_dec t t'
  then 1
  else 0.
Definition AddTiming (t1 t2: TimingMap): TimingMap := fun x => t1 x + t2 x.

Notation "a ++ b" := (AddTiming a b) (at level 60, right associativity).

Inductive ExpressionBigStep {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel}: Expression -> MemStore -> Level -> TimingMap -> Primitive -> Level -> Type :=
| ConsBigStep (prim: Primitive) {pc k j: Level} (joinProof: Join rel pc k j) (mu: MemStore): @ExpressionBigStep binop_eval rel latticeProof (PrimitiveExpression prim k) mu pc (SingleTiming CONST) prim j
                                                                                                               
| VarBigStep (x: Var) (mu: MemStore) (pc: Level): @ExpressionBigStep binop_eval rel latticeProof (VarExpression x) mu pc (SingleTiming VAR) (fst (mu x)) (snd (mu x))
                                                                    
| OperBigStep (oper: BinOp) {mu: MemStore}{e1 e2: Expression} {pc k1 k2 joink1k2: Level} {T1 T2: TimingMap} {n1 n2: Primitive} (p1: @ExpressionBigStep binop_eval rel latticeProof e1 mu pc T1 n1 k1) (p2: @ExpressionBigStep binop_eval rel latticeProof e2 mu pc T2 n2 k2) (joinProof: Join rel k1 k2 joink1k2): @ExpressionBigStep binop_eval rel latticeProof (BinOpExpression oper e1 e2) mu pc (T1 ++ T2 ++ (SingleTiming (OPER oper))) (binop_eval oper n1 n2) joink1k2
                                                                                                                                                                                                                                                                           
| CommaBigStep {e1 e2: Expression} {mu: MemStore} {pc k1 k2: Level} {t1 t2: TimingMap} {n1 n2: Primitive} (p1: @ExpressionBigStep binop_eval rel latticeProof e1 mu pc t1 n1 k1) (p2: @ExpressionBigStep binop_eval rel latticeProof e2 mu pc t2 n2 k2): @ExpressionBigStep binop_eval rel latticeProof (CommaExpression e1 e2) mu pc (t1 ++ t2 ++ (SingleTiming COMMA)) n2 k2.



Inductive CommandBigStep {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel}: Command -> MemStore -> Level -> TimingMap -> MemStore -> Type :=
| SkipBigStep (mu: MemStore) (pc: Level)
  : CommandBigStep SkipCommand mu pc (SingleTiming SKIP) mu
                   
| SeqBigStep {c1 c2: Command} {mu mu' mu'': MemStore} {pc: Level} {T1 T2: TimingMap}
    (p1: CommandBigStep c1 mu pc T1 mu')
    (p2: CommandBigStep c2 mu' pc T2 mu'')
  : CommandBigStep (SeqCommand  c1 c2) mu pc (T1 ++ T2 ++ (SingleTiming SEQ)) mu''
                   
| WhileFBigStep {e: Expression} {mu: MemStore} {pc k: Level} {T: TimingMap} (c: Command) {n: Primitive}
    (expressionEvalProof: (@ExpressionBigStep binop_eval rel latticeProof e mu pc T n k))
    (falseProof: n = TruePrimitive -> False)
  : CommandBigStep (WhileCommand e c) mu pc (T++(SingleTiming WHILEF)) mu
      
|  WhileTBigStep {e: Expression} {mu mu' mu'': MemStore} {pc k: Level} {T1 T2 T3: TimingMap} {c: Command} 
     (expressionEvalProof: (@ExpressionBigStep binop_eval rel latticeProof e mu pc T1 TruePrimitive k))
     (commandProof: CommandBigStep c mu pc T2 mu')
     (restLoopProof: CommandBigStep (WhileCommand e c) mu' pc T3 mu'')
     (lowProof: rel k pc)
  : CommandBigStep (WhileCommand e c) mu pc (SingleTiming WHILET ++ T1 ++ T2 ++ T3) mu''

| AssnBigStepEq {e: Expression} {mu: MemStore} {x: Var} {pc k: Level} {T: TimingMap} {n: Primitive}
    (eproof: @ExpressionBigStep binop_eval rel latticeProof e mu pc T n k)
    (eqProof: ((snd (mu x)) = pc) \/ ((rel (snd (mu x)) pc) -> False))
  : CommandBigStep (AssnCommand x e) mu pc (SingleTiming ASSN ++ T) (MemUpdate mu x n k)
                   
| IfHighBigStep {e: Expression} {mu mu': MemStore} {pc k: Level} {n: Primitive} {T1 T2: TimingMap} {n: Primitive} {c1 c2: Command}
    (eProof: @ExpressionBigStep binop_eval rel latticeProof e mu pc T1 n k)
    (debProof: DebranchBigStep (Debranch (IfCommand e c1 c2) true pc) mu pc T2 mu')
    (relProof: rel k pc -> False)
  : CommandBigStep (IfCommand e c1 c2) mu pc (SingleTiming IF_HIGH ++ T1 ++ T2) mu' 
                   
| IfLowBigStep
    {e: Expression} {mu mu': MemStore} {pc k: Level} {n: Primitive} {T1 T2: TimingMap} (c1 c2: Command)
    (eProof: @ExpressionBigStep binop_eval rel latticeProof e mu pc T1 n k)
    (relProof: rel k pc)
    (commandProof: let c := match n with | TruePrimitive => c1 | _ => c2 end in
                   CommandBigStep c mu pc T2 mu')
  : CommandBigStep (IfCommand e c1 c2) mu pc (SingleTiming IF_LOW ++ T1 ++ T2) mu'
with DebranchBigStep {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel}: DebranchCommand -> MemStore -> Level -> TimingMap -> MemStore -> Type :=

| DebSkipBigStep
    (n: bool) (l pc: Level) (mu: MemStore)
  : DebranchBigStep (Debranch SkipCommand n l) mu pc (SingleTiming DEB_SKIP) mu
                    
| DebAssnTrueBigStep {x: Var} {e: Expression} {l pc: Level} {mu mu': MemStore} {T: TimingMap}
    (evalProof: CommandBigStep (AssnCommand x (CommaExpression (VarExpression x) e)) mu pc T mu')
  : DebranchBigStep (Debranch (AssnCommand x e) true l) mu pc (SingleTiming DEB_ASSN ++ T) mu'
                    
| DebAssnFalseBigStep {x: Var} {e: Expression} {l pc: Level} {mu mu': MemStore} {T: TimingMap}
    (evalProof: CommandBigStep (AssnCommand x (CommaExpression e (VarExpression x))) mu pc T mu')
  : DebranchBigStep (Debranch (AssnCommand x e) false l) mu pc (SingleTiming DEB_ASSN ++ T) mu'
                    
| DebSeqBigStep {c1 c2: Command} {n: bool} {l: Level} {mu mu' mu'': MemStore} {l pc: Level} {T1 T2: TimingMap}
    (p1: DebranchBigStep (Debranch c1 n l) mu pc T1 mu')
    (p2: DebranchBigStep (Debranch c2 n l) mu' pc T2 mu'')
  : DebranchBigStep (Debranch (SeqCommand c1 c2) n l) mu pc (SingleTiming DEB_SEQ ++ T1 ++ T2) mu''
                    
| DebIfHighBigStep {e: Expression} {c1 c2: Command} {mu mu' mu'': MemStore} {l pc kl kpc: Level} {n: bool} {n': Primitive} {T1 T2 T3 T4: TimingMap}
    (p1: @ExpressionBigStep binop_eval rel latticeProof e mu l T1 n' kl)
    (p2: @ExpressionBigStep binop_eval rel latticeProof e mu pc T2 n' kpc)
    (relProof: rel kl l -> False)
    (p3: DebranchBigStep (Debranch c1 (andb (PrimToBool n') n) l) mu kpc T3 mu')
    (p4: DebranchBigStep (Debranch c2 (andb (negb (PrimToBool n')) n) l) mu' kpc T4 mu'')
  : DebranchBigStep (Debranch (IfCommand e c1 c2) n l) mu pc (SingleTiming DEB_IF_HIGH ++ T1 ++ T2 ++ T3 ++ T4) mu''
| DebIfLowBigStep
    {e: Expression} {mu mu': MemStore} {pc k l: Level} {n: bool} {n': Primitive} {T1 T2: TimingMap} (c1 c2: Command)
    (eProof: @ExpressionBigStep binop_eval rel latticeProof e mu pc T1 n' k)
    
    (relProof: rel k pc)
    (commandProof: let d := match n' with | TruePrimitive => (Debranch c1 n l) | _ => (Debranch c2 n l) end in
                   DebranchBigStep d mu pc T2 mu')
  : DebranchBigStep (Debranch (IfCommand e c1 c2) n l) mu pc (SingleTiming DEB_IF_LOW ++ T1 ++ T2) mu'
| DebWhileFBigStep {e: Expression} {mu: MemStore} {pc k l: Level} {T: TimingMap} (c: Command) {n: bool} {n': Primitive}
    (expressionEvalProof: (@ExpressionBigStep binop_eval rel latticeProof e mu pc T n' k))
    (falseProof: n' = TruePrimitive -> False)
  : DebranchBigStep (Debranch (WhileCommand e c) n l) mu pc (T++(SingleTiming DEB_WHILEF)) mu
      
|  DebWhileTBigStep {e: Expression} {mu mu' mu'': MemStore} {pc k l kl kpc: Level} {T1 T1' T2 T3: TimingMap} {c: Command} {n: bool}
     (expressionEvalProofl: (@ExpressionBigStep binop_eval rel latticeProof e mu l T1 TruePrimitive kl))
     (expressionEvalProofpc: (@ExpressionBigStep binop_eval rel latticeProof e mu pc T1' TruePrimitive kpc))
     (commandProof: DebranchBigStep (Debranch c n l) mu kpc T2 mu')
     (restLoopProof: DebranchBigStep (Debranch (WhileCommand e c) n l) mu' pc T3 mu'')
     (lowProof: rel k l)
  : DebranchBigStep (Debranch (WhileCommand e c) n l) mu pc (SingleTiming DEB_WHILET ++ T1 ++ T1' ++ T2 ++ T3) mu''.

                  


  
