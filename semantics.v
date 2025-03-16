From Coq Require Import Program.Equality.
From Coq Require Import Lists.List.

Definition x := fun x => fun y => x + y.
Check x.
Inductive PartialOrder {A: Type} (rel: A -> A -> Type) : Type:= 
| PartialOrderConstructor  (rel_refl: forall (a: A), rel a a) (rel_trans: forall (a b c: A), rel a b -> rel b c -> rel a c) (rel_antisym: forall (a b: A), a <> b -> rel a b -> rel b a -> False).

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
| ConstBigStep (prim: Primitive) {pc k j: Level} (joinProof: Join rel pc k j) (mu: MemStore): ExpressionBigStep (PrimitiveExpression prim k) mu pc (SingleTiming CONST) prim j
                                                                                                               
| VarBigStep(x: Var) (mu: MemStore) (pc j: Level) (joinProof: Join rel pc (snd (mu x)) j): ExpressionBigStep (VarExpression x) mu pc (SingleTiming VAR) (fst (mu x)) j
                                                                    
| OperBigStep (oper: BinOp) {mu: MemStore}{e1 e2: Expression} {pc k1 k2 joink1k2: Level} {T1 T2: TimingMap} {n1 n2: Primitive} (p1: ExpressionBigStep  e1 mu pc T1 n1 k1) (p2: ExpressionBigStep  e2 mu pc T2 n2 k2) (joinProof: Join rel k1 k2 joink1k2): ExpressionBigStep  (BinOpExpression oper e1 e2) mu pc (T1 ++ T2 ++ (SingleTiming (OPER oper))) (binop_eval oper n1 n2) joink1k2.



Inductive CommandBigStep {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel}: Command -> MemStore -> Level -> TimingMap -> MemStore -> Type :=
| SkipBigStep (mu: MemStore) (pc: Level)
  : CommandBigStep SkipCommand mu pc (SingleTiming SKIP) mu
                   
| SeqBigStep {c1 c2: Command} {mu mu' mu'': MemStore} {pc: Level} {T1 T2: TimingMap}
    (p1: CommandBigStep c1 mu pc T1 mu')
    (p2: CommandBigStep c2 mu' pc T2 mu'')
  : CommandBigStep (SeqCommand  c1 c2) mu pc (T1 ++ T2 ++ (SingleTiming SEQ)) mu''
                   
| WhileFBigStep {e: Expression} {mu: MemStore} {pc k: Level} {T: TimingMap} (c: Command) {n: Primitive}
    (expressionEvalProof: (@ExpressionBigStep binop_eval rel latticeProof e mu pc T n k))
    (falseProof: n <> TruePrimitive)
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
                    
| DebAssnTrueBigStep  {e: Expression} {l pc k: Level} {mu mu': MemStore} {T: TimingMap} {n: Primitive}
    (x: Var)
    (evalProof: @ExpressionBigStep binop_eval rel latticeProof e mu pc T n k)
    (eqProof: ((snd (mu x)) = pc) \/ ((rel (snd (mu x)) pc) -> False))
  : DebranchBigStep (Debranch (AssnCommand x e) true l) mu pc (SingleTiming DEB_ASSN ++ T) (MemUpdate mu x n k) 
                    
| DebAssnFalseBigStep {e: Expression} {l pc k: Level} {mu: MemStore} {T: TimingMap} {n: Primitive}
    (x: Var)
    (evalProof: @ExpressionBigStep binop_eval rel latticeProof e mu pc T n k)
    (eqProof: ((snd (mu x)) = pc) \/ ((rel (snd (mu x)) pc) -> False))
  : DebranchBigStep (Debranch (AssnCommand x e) false l) mu pc (SingleTiming DEB_ASSN ++ T) mu
                    
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
    (eProof: @ExpressionBigStep binop_eval rel latticeProof e mu l T1 n' k)
    
    (relProof: rel k l)
    (commandProof: let d := match n' with | TruePrimitive => (Debranch c1 n l) | _ => (Debranch c2 n l) end in
                   DebranchBigStep d mu pc T2 mu')
  : DebranchBigStep (Debranch (IfCommand e c1 c2) n l) mu pc (SingleTiming DEB_IF_LOW ++ T1 ++ T2) mu'
| DebWhileFBigStep {e: Expression} {mu: MemStore} {k l: Level} {T: TimingMap} {n': Primitive}
    (c: Command)
    (n: bool)
    (pc: Level)
    (expressionEvalProof: (@ExpressionBigStep binop_eval rel latticeProof e mu l T n' k))
    (falseProof: n' <> TruePrimitive)
  : DebranchBigStep (Debranch (WhileCommand e c) n l) mu pc (T++(SingleTiming DEB_WHILEF)) mu
      
|  DebWhileTBigStep {e: Expression} {mu mu' mu'': MemStore} {pc l kl kpc: Level} {T1 T1' T2 T3: TimingMap} {c: Command} {n: bool}
     (expressionEvalProof: (@ExpressionBigStep binop_eval rel latticeProof e mu l T1 TruePrimitive kl))
     (commandProof: DebranchBigStep (Debranch c n l) mu pc T2 mu')
     (restLoopProof: DebranchBigStep (Debranch (WhileCommand e c) n l) mu' pc T3 mu'')
     (lowProof: rel kl l)
  : DebranchBigStep (Debranch (WhileCommand e c) n l) mu pc (SingleTiming DEB_WHILET ++ T1 ++ T2 ++ T3) mu''.

                  
Inductive ValueObservationalEquivalent {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel}: Primitive -> Level -> Level -> Primitive -> Level -> Type :=
| LowProof {n1 n2: Primitive} {l1 l2 l: Level} (nEq: n1 = n2) (lEq: l1 = l2) : ValueObservationalEquivalent n1 l1 l n2 l2
| HighProof (n1 n2: Primitive) {l1 l2 l: Level} (l1High: rel l1 l -> False) (l2High: rel l2 l -> False): ValueObservationalEquivalent n1 l1 l n2 l2.

Definition MemStoreObservationalEquivalent {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel} (mu1: MemStore) (l: Level) (mu2: MemStore): Type := forall (x: Var), @ValueObservationalEquivalent rel latticeProof (fst (mu1 x)) (snd (mu1 x)) l  (fst (mu2 x)) (snd (mu2 x)).

  
Lemma JoinEq: forall {rel: Level -> Level -> Type} (latticeProof: JoinSemilattice rel) {a b j1 j2: Level}, Join rel a b j1 -> Join rel a b j2 -> j1 = j2.
Proof.
  intros. destruct X; destruct X0; destruct latticeProof; destruct OrdProof. destruct (level_eq_dec join join0).
  - assumption.
  -  specialize (pleast join0 pleft0 pright0); specialize (pleast0 join pleft pright). specialize (rel_antisym join join0 n pleast pleast0). contradiction.
Qed.
Lemma JoinSym: forall {rel: Level -> Level -> Type} (latticeProof: JoinSemilattice rel) {a b join: Level}, Join rel a b join -> Join rel b a join.
Proof.
  intros. destruct X. constructor; (try assumption).
  - intros. apply (pleast ub X0 X).
Qed.

Lemma JoinHigh: forall {rel: Level -> Level -> Type} (latticeProof: JoinSemilattice rel) {H L X joinHX: Level}, (Join rel H X joinHX) -> (rel H L -> False) -> (rel joinHX L -> False).
Proof.
  intros. destruct X0; destruct latticeProof; destruct OrdProof. apply H0. apply (rel_trans _ _ _ pleft X1).
Qed.
  
Lemma ExpressionLabelLowerBound: forall  {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel} {e: Expression} {mu: MemStore} {l k: Level} {T: TimingMap}  {n: Primitive} (proof: @ExpressionBigStep binop_eval rel latticeProof e mu l T n k), rel l k. 
Proof.
  intros. induction proof.
  - destruct joinProof. assumption.
  - destruct joinProof. assumption.
  - destruct latticeProof. destruct OrdProof. destruct joinProof. apply (rel_trans _ _ _  IHproof1 pleft).
  
Qed.

Lemma ExpressionLabelLowestBound: forall  {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel} {e: Expression} {mu: MemStore} {l k: Level} {T: TimingMap}  {n: Primitive} (proof: @ExpressionBigStep binop_eval rel latticeProof e mu l T n k), rel k l -> l = k.
Proof.
  intros. pose proof (ExpressionLabelLowerBound proof). destruct (level_eq_dec l k).
  - assumption.
  - destruct latticeProof; destruct OrdProof. pose proof (rel_antisym _ _ n0 X0 X). contradiction.
Qed.


Lemma ExpressionHigherContext: forall {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel} {e: Expression} {mu: MemStore} {l kl h kh: Level} {T1 T2: TimingMap}  {n1 n2: Primitive} (proof1: @ExpressionBigStep binop_eval rel latticeProof e mu l T1 n1 kl) (proof2: @ExpressionBigStep binop_eval rel latticeProof e mu h T2 n2 kh), rel l h -> rel kl l ->  kh = h.
Proof.
  intros. pose proof (ExpressionLabelLowestBound proof1 X0). subst. clear X0.

  dependent induction e; dependent destruction proof2; dependent destruction proof1.
  - assert(Joinpc0: Join rel pc0 k pc0). {
      destruct latticeProof; destruct OrdProof.
        assert (ubProof: forall ub, rel pc0 ub -> rel k ub -> rel pc0 ub) by (intros; assumption).
        destruct joinProof; destruct joinProof0.
        constructor; auto. apply (rel_trans _ _ _ pright X).
    } 

    apply (JoinEq latticeProof joinProof0 Joinpc0).
  - assert(Joinpc0: Join rel pc0 (snd (mu x0)) pc0). {
      destruct latticeProof; destruct OrdProof.
        assert (ubProof: forall ub, rel pc0 ub -> rel (snd (mu x0)) ub -> rel pc0 ub) by (intros; assumption).
        destruct joinProof; destruct joinProof0.
        constructor; auto. apply (rel_trans _ _ _ pright X).
    } apply (JoinEq latticeProof joinProof0 Joinpc0).
  -
    destruct joinProof.
    pose proof (ExpressionLabelLowestBound proof1_1 pleft).
    pose proof (ExpressionLabelLowestBound proof1_2 pright).
    subst a b. clear pleft pleast pright.

    pose proof (IHe1 _ _ _ _ _ _ _ _ proof1_1 proof2_1 X).
    pose proof (IHe2 _ _ _ _ _ _ _ _ proof1_2 proof2_2 X).
    subst k0 k3.
    assert (Join rel pc0 pc0 pc0). {
      destruct latticeProof; destruct OrdProof.
      constructor; auto; apply rel_refl.
    } apply (JoinEq latticeProof joinProof0 X0).

Qed.
    


Lemma LowerRelWorse: forall {rel: Level -> Level -> Type} (latticeProof: JoinSemilattice rel) {LL L H: Level}, rel LL L -> (rel H L -> False) -> (rel H LL -> False).
Proof.
  intros; destruct latticeProof; destruct OrdProof. apply H0. apply (rel_trans _ _ _ X0 X).
Qed.


Lemma BiggerFish {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel}: forall {LL L H: Level},
    LL <> L -> rel LL L -> rel L H -> (rel H LL -> False).
Proof.
  intros. destruct latticeProof; destruct OrdProof.  destruct (level_eq_dec L H).
  - subst. apply (rel_antisym _ _ H0 X X1).
  - specialize (rel_trans _ _ _ X0 X1). apply (rel_antisym _ _ H0 X rel_trans).

Qed.
  
Lemma MemStoreEquivalenceImplExpressionEquivalence:
  forall  {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel} {e: Expression} {mu1 mu2: MemStore} {l k1 k2: Level} {n1 n2: Primitive} {T1 T2: TimingMap}
          (p1: @ExpressionBigStep binop_eval rel latticeProof e mu1 l T1 n1 k1)
          (p2: @ExpressionBigStep binop_eval rel latticeProof e mu2 l T2 n2 k2)
          (memEqProof: @MemStoreObservationalEquivalent rel latticeProof mu1 l mu2),
    @ValueObservationalEquivalent rel latticeProof n1 k1 l n2 k2.
Proof.
  intros.


  dependent induction e; dependent destruction p1; dependent destruction p2.
  
  - 
    pose proof (JoinEq latticeProof joinProof0 joinProof).
    subst j. constructor; auto.

  -  specialize (memEqProof x0). destruct memEqProof.
    + subst. pose proof (JoinEq latticeProof joinProof joinProof0). subst. constructor; auto.
    + specialize (JoinHigh latticeProof (JoinSym latticeProof joinProof) l1High);
        specialize (JoinHigh latticeProof (JoinSym latticeProof joinProof0) l2High); intros. apply (HighProof n1 n2 H0 H).
  -  specialize (IHe1 _ _ _ _ _ _ _ _ _  p1_1 p2_1 memEqProof); specialize (IHe2 _ _ _ _ _ _ _ _ _  p1_2 p2_2 memEqProof). destruct IHe1; destruct IHe2.
     + subst. pose proof (JoinEq latticeProof joinProof joinProof0). subst. constructor; auto.
     + subst. specialize (JoinHigh latticeProof (JoinSym latticeProof joinProof) l1High);
         specialize (JoinHigh latticeProof (JoinSym latticeProof joinProof0) l2High); intros. apply (HighProof _ _ H0 H).
     + subst. specialize (JoinHigh latticeProof  joinProof l1High);
         specialize (JoinHigh latticeProof  joinProof0 l2High); intros. apply (HighProof _ _ H0 H).
     + subst. specialize (JoinHigh latticeProof  joinProof l1High);
         specialize (JoinHigh latticeProof  joinProof0 l2High); intros. apply (HighProof _ _ H0 H).
Qed.

Lemma TrickleDownEquivalence: forall {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel} {k l: Level} {mu1 mu2: MemStore} (downProof: rel l k) (highProof: @MemStoreObservationalEquivalent rel latticeProof mu1 k mu2), @MemStoreObservationalEquivalent rel latticeProof mu1 l mu2.
Proof.
  intros. unfold MemStoreObservationalEquivalent. intros. destruct (highProof x0).
  - subst. constructor; auto.
  - specialize (LowerRelWorse latticeProof downProof l1High); specialize (LowerRelWorse latticeProof downProof l2High); intros.
    apply (HighProof _ _ H0 H).
Qed.

Lemma EqMemStoreImplEqPrimTim {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel} :
  forall {e: Expression} {pc k: Level} {mu: MemStore} {T: TimingMap} {n: Primitive} (pc': Level),
    @ExpressionBigStep binop_eval rel latticeProof e mu pc T n k ->
    EX (fun k' => @ExpressionBigStep binop_eval rel latticeProof e mu pc' T n k').
Proof.
  intros. dependent induction e; dependent destruction X.
  - remember latticeProof; destruct j0. destruct (JoinProof pc' k).
    apply (EX_intro _ x0 (ConstBigStep prim j0 mu)).
  - remember latticeProof; destruct j0. destruct (JoinProof pc' (snd (mu x0))). apply (EX_intro _ x1). constructor; assumption.
  - specialize (IHe1 _ _ _ _ _ pc' X1). specialize (IHe2 _ _ _ _ _ pc' X2). destruct IHe1; destruct IHe2. remember latticeProof; destruct j. destruct (JoinProof x0 x1). apply (EX_intro _ x2). apply (OperBigStep binop e e0 j).
Qed.


(* Trying to establish a consistent way to deal with inductive proofds on WhileCommands and Debranch(WhileCommand)s*)

(*First doing it on WhileCommands, corresponding stuff on Debranch(WhileCommands)s will follow. *)

Inductive LoopLengthCommand {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel} : Level -> MemStore -> Expression -> Command -> MemStore -> nat -> Type :=
| LoopLengthCommand0 {mu: MemStore} {e: Expression} {n: Primitive} {pc k: Level} {T: TimingMap}
    (c: Command)
    (expressionEvalProof: @ExpressionBigStep binop_eval rel latticeProof e mu pc T n k)
    (primProof: n <> TruePrimitive)
  : LoopLengthCommand pc mu e c mu 0

| LoopLengthCommandSn {mu mu' mu'': MemStore} {e: Expression} {n: nat} {pc k: Level} {Te Tc Tw: TimingMap} {c: Command}
    (expressionProof: @ExpressionBigStep binop_eval rel latticeProof e mu pc Te TruePrimitive k)
    (commandProof: @CommandBigStep binop_eval rel latticeProof c mu pc Tc mu')
    (whileProof: @CommandBigStep binop_eval rel latticeProof (WhileCommand e c) mu' pc Tw mu'')
    (indProof: LoopLengthCommand pc mu' e c mu'' n)
    (relProof: rel k pc)
  : LoopLengthCommand pc mu e c mu'' (S n).

Lemma AlwaysLoopLengthCommand {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel}:
  forall {e: Expression} {c: Command} {mu mu': MemStore} {pc: Level} {T: TimingMap},
    @CommandBigStep binop_eval rel latticeProof (WhileCommand e c) mu pc T mu' ->
    EX (fun n => @LoopLengthCommand binop_eval rel latticeProof pc mu e c mu' n).
Proof.
  intros.
  dependent induction X.
  - apply (EX_intro _ 0 (LoopLengthCommand0  c expressionEvalProof falseProof)).
  - clear IHX1. assert (WhileCommand e c = WhileCommand e c) by auto.  specialize (IHX2 H); clear H;  destruct IHX2. apply (EX_intro _ (S x0) (LoopLengthCommandSn expressionEvalProof X1 X2 l lowProof)).
Qed.

Lemma MemStoreEquivalenceImplLoopLengthCommandEq {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel}:
  forall {e: Expression} {c: Command} {mu1 mu1' mu2 mu2': MemStore}  {pc: Level}  {n1 n2: nat}
         (cMemEq: forall  (mu1 mu2 mu1' mu2' : MemStore) (pc : Level) (T1 T2 : TimingMap),
        @CommandBigStep binop_eval rel latticeProof c  mu1 pc T1 mu1' ->
        @CommandBigStep binop_eval rel latticeProof c mu2 pc T2 mu2' ->
        @MemStoreObservationalEquivalent rel latticeProof mu1 pc mu2 -> @MemStoreObservationalEquivalent rel latticeProof mu1' pc mu2'),
    @LoopLengthCommand binop_eval rel latticeProof pc mu1 e c mu1' n1 ->
    @LoopLengthCommand binop_eval rel latticeProof pc mu2 e c mu2' n2 ->
    @MemStoreObservationalEquivalent rel latticeProof mu1 pc mu2 ->
    n1 = n2.
Proof.
  intros.  generalize dependent mu2. generalize dependent mu2'. generalize dependent mu1'. generalize dependent mu1. dependent induction n1; intros; dependent destruction X; dependent destruction X0.
    + reflexivity.
    + pose proof (MemStoreEquivalenceImplExpressionEquivalence expressionEvalProof expressionProof X1). destruct H; contradiction.
    + pose proof (MemStoreEquivalenceImplExpressionEquivalence expressionProof expressionEvalProof X1). destruct H; subst; contradiction.
    + pose proof (cMemEq _ _ _ _ _ _ _  commandProof commandProof0 X1).
      specialize (IHn1 _ cMemEq _ _ X _ _  X0 X2).
      subst. reflexivity.
Qed.
                       
    
(* Same but for Debranch *)

Inductive LoopLengthDebranch {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel} : Level -> MemStore -> Expression -> Command -> bool -> Level -> MemStore -> nat -> Type :=
| LoopLengthDebranch0 {mu: MemStore} {e: Expression} {n': Primitive} {l k: Level} {T: TimingMap}
    (c: Command) (n: bool) (pc: Level)
    (expressionEvalProof: @ExpressionBigStep binop_eval rel latticeProof e mu l T n' k)
    (primProof: n' <> TruePrimitive)
  : LoopLengthDebranch pc mu e c n l mu 0

| LoopLengthDebranchSn {mu mu' mu'': MemStore} {e: Expression} {x: nat} {pc l kl: Level} {Te Tc Tw: TimingMap} {c: Command} {n: bool}
    (expressionEvalProof: (@ExpressionBigStep binop_eval rel latticeProof e mu l Te TruePrimitive kl))
    (commandProof: @DebranchBigStep binop_eval rel latticeProof (Debranch c n l) mu pc Tc mu')
    (restLoopProof: @DebranchBigStep binop_eval rel latticeProof (Debranch (WhileCommand e c) n l) mu' pc Tw mu'')
    (indProof: LoopLengthDebranch pc mu' e c n l mu'' x)
    (lowProof: rel kl l)
    
  : LoopLengthDebranch pc mu e c n l mu'' (S x).

Lemma AlwaysLoopLengthDebranch {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel}:
  forall {e: Expression} {c: Command} {n: bool} {mu mu': MemStore} {pc l: Level} {T: TimingMap},
    @DebranchBigStep binop_eval rel latticeProof (Debranch (WhileCommand e c) n l) mu pc T mu' ->
    EX (fun x => @LoopLengthDebranch binop_eval rel latticeProof pc mu e c n l mu' x).
Proof.
  intros.
  dependent induction X.
  -  apply (EX_intro _ 0  (LoopLengthDebranch0  c n pc expressionEvalProof falseProof)).
  - clear IHX1. assert (Debranch (WhileCommand e c) n l = Debranch (WhileCommand e c) n l) by auto.  specialize (IHX2 H); clear H;  destruct IHX2.
    apply (EX_intro _ (S x0) (LoopLengthDebranchSn expressionEvalProof X1 X2 l0 lowProof)).
Qed.

Lemma MemStoreEquivalenceImplLoopLengthDebranchEq {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel}:
  forall {e: Expression} {c: Command} {n1 n2: bool} {mu1 mu1' mu2 mu2': MemStore}  {pc1 pc2 l: Level} {x1 x2: nat}
         
         (debcMemEq: forall (n1 n2 : bool) (mu1 mu2 mu1' mu2' : MemStore) (l pc1 pc2 : Level) (T1 T2 : TimingMap),
        @DebranchBigStep binop_eval rel latticeProof (Debranch c n1 l) mu1 pc1 T1 mu1' ->
        @DebranchBigStep binop_eval rel latticeProof(Debranch c n2 l) mu2 pc2 T2 mu2' ->
        @MemStoreObservationalEquivalent rel latticeProof mu1 l mu2 ->
        rel l pc1 -> l <> pc1 -> rel l pc2 -> l <> pc2 -> @MemStoreObservationalEquivalent rel latticeProof mu1' l mu2'),
    rel l pc1 -> l <> pc1 -> rel l pc2 -> l <> pc2 ->
    @LoopLengthDebranch binop_eval rel latticeProof pc1 mu1 e c n1 l mu1' x1 ->
    @LoopLengthDebranch binop_eval rel latticeProof pc2 mu2 e c n2 l mu2' x2 ->
    @MemStoreObservationalEquivalent rel latticeProof mu1 l mu2 ->
    x1 = x2.
Proof.
  intros.  generalize dependent mu2; generalize dependent mu2'; generalize dependent mu1'; generalize dependent mu1. dependent induction x1; intros; dependent destruction X1; dependent destruction X2.
    + reflexivity.
    + assert (n' = TruePrimitive). {
        
        pose proof (MemStoreEquivalenceImplExpressionEquivalence expressionEvalProof expressionEvalProof0 X3).
        pose proof (ExpressionLabelLowestBound expressionEvalProof0 lowProof); subst kl.
        remember latticeProof; destruct j; destruct OrdProof. 
        dependent destruction H1.
        - auto.
        -  specialize (l2High (rel_refl l)). contradiction.
      } contradiction.
    +  assert (n' = TruePrimitive). {
        pose proof (MemStoreEquivalenceImplExpressionEquivalence expressionEvalProof expressionEvalProof0 X3).
        pose proof (ExpressionLabelLowestBound expressionEvalProof lowProof); subst kl.
        remember latticeProof; destruct j; destruct OrdProof. 
        dependent destruction H1.
        - auto.
        -  specialize (l1High (rel_refl l1)). contradiction.
       } contradiction. 
    +

      pose proof (ExpressionLabelLowestBound expressionEvalProof lowProof); subst kl;
        pose proof (ExpressionLabelLowestBound expressionEvalProof0 lowProof0); subst kl0; clear lowProof lowProof0.
      
      
      pose proof (debcMemEq _ _ _ _ _ _ _ _ _ _ _ commandProof commandProof0 X3 X H X0 H0).
      specialize (IHx1 _ debcMemEq X H X0 H0 _ _ X1 _ _  X2 X4).
      subst. reflexivity.
Qed.
                     
(*
  The main idea of defining these was to allow treating While Loops as an inductive object based on their loop length.
 *)
(*
Lemma HighDebranchImplLowMemEq {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel} : forall {c: command}  {n: bool} {l H L: Level} {mu1 mu1' mu2 mu2': MemStore} {T: TimingMap}
 *)

Theorem DebranchPreservesMemEq {binop_eval: BinOp -> Primitive -> Primitive -> Primitive} {rel: Level -> Level -> Type} {latticeProof: JoinSemilattice rel} : forall  {c: Command} {n1 n2: bool} {mu1 mu2 mu1' mu2': MemStore} {l pc1 pc2: Level} {T1 T2: TimingMap}
         (p1: @DebranchBigStep binop_eval rel latticeProof (Debranch c n1 l) mu1 pc1 T1 mu1')
         (p2: @DebranchBigStep binop_eval rel latticeProof (Debranch c n2 l) mu2 pc2 T2 mu2')
         (memEq: @MemStoreObservationalEquivalent rel latticeProof mu1 l mu2)
         (l_rel_pc1: rel l pc1)
         (l_not_pc1: l <> pc1)
         (l_rel_pc2: rel l pc2)
         (l_not_pc2: l <> pc2),
    @MemStoreObservationalEquivalent rel latticeProof mu1' l mu2'.
Proof.
  intros. dependent induction c.
  
  -  dependent destruction p1; dependent destruction p2. assumption.
    
  -  dependent destruction p1; dependent destruction p2; unfold MemStoreObservationalEquivalent in *; unfold MemUpdate; unfold t_update; intros; destruct (var_eq_dec x0 x1); auto; simpl; subst.
       
     + pose proof (ExpressionLabelLowerBound evalProof); pose proof (ExpressionLabelLowerBound evalProof0). Check @BiggerFish. pose proof (@BiggerFish rel latticeProof _ _ _ l_not_pc1 l_rel_pc1 X);  pose proof (@BiggerFish rel latticeProof _ _ _ l_not_pc2 l_rel_pc2 X0). apply (HighProof _ _ H H0).

     + pose proof (ExpressionLabelLowerBound evalProof); pose proof (@BiggerFish rel latticeProof _ _ _ l_not_pc1 l_rel_pc1 X); clear X. assert (H0: rel (snd (mu0 x1)) l -> False). {
         destruct eqProof0.
         + subst. remember latticeProof; destruct j; destruct OrdProof. apply (rel_antisym _ _ l_not_pc2 l_rel_pc2).
         + Check @LowerRelWorse. apply (@LowerRelWorse rel latticeProof _ _ _ l_rel_pc2 H0).
       } apply (HighProof _ _ H H0).

     + pose proof (ExpressionLabelLowerBound evalProof0); pose proof (@BiggerFish rel latticeProof _ _ _ l_not_pc2 l_rel_pc2 X); clear X. assert (H0: rel (snd (mu x1)) l -> False). {
         destruct eqProof.
         + subst. remember latticeProof; destruct j; destruct OrdProof. apply (rel_antisym _ _ l_not_pc1 l_rel_pc1).
         + Check @LowerRelWorse. apply (@LowerRelWorse rel latticeProof _ _ _ l_rel_pc1 H0).
       } apply (HighProof _ _ H0 H).

  
  -  dependent destruction p1; dependent destruction p2. specialize (IHc1 _ _ _ _ _ _ _ _ _ _ _ p1_1 p2_1 memEq l_rel_pc1 l_not_pc1 l_rel_pc2 l_not_pc2). apply (IHc2 _ _ _ _ _ _ _ _ _ _ _ p1_2 p2_2 IHc1 l_rel_pc1 l_not_pc1 l_rel_pc2 l_not_pc2).

  - dependent destruction p2; dependent destruction p1.
    + pose proof (ExpressionLabelLowerBound p2); pose proof (ExpressionLabelLowerBound p3).

      
      remember latticeProof; destruct j; destruct OrdProof.

      pose proof (rel_trans _ _ _ l_rel_pc1 X).
      pose proof (rel_trans _ _ _ l_rel_pc2 X0).

      assert (eq: l <> kpc /\ l <> kpc0). {
        split.
        - destruct (level_eq_dec l kpc); auto. subst. pose proof (rel_antisym _ _ l_not_pc1 l_rel_pc1 X). contradiction.
        - destruct (level_eq_dec l kpc0); auto. subst. pose proof (rel_antisym _ _ l_not_pc2 l_rel_pc2 X0). contradiction.
      } destruct eq as [eq  eq0].
      
      specialize (IHc1 _ _ _ _ _ _ _ _ _ _ _ p1_1 p2_1 memEq X1 eq X2 eq0).
      apply (IHc2 _ _ _ _ _ _ _ _ _ _ _ p1_2 p2_2 IHc1 X1 eq X2 eq0).
    + assert(k = kl). {
        Check @MemStoreEquivalenceImplExpressionEquivalence.
        pose proof (MemStoreEquivalenceImplExpressionEquivalence eProof p0 memEq).
        destruct H.
        - assumption.
        - contradiction.
      } subst. contradiction.

    + assert(k = kl). {
        
        pose proof (MemStoreEquivalenceImplExpressionEquivalence p1 eProof memEq).
        destruct H.
        - auto.
        - contradiction.
      } subst. contradiction.
    + assert (n' = n'0 /\ k0 = k). {
        
        pose proof (MemStoreEquivalenceImplExpressionEquivalence eProof eProof0 memEq).
        destruct H.
        - split; auto.
        - contradiction.
      } destruct H. subst.
      destruct  n'0;
        try (apply (IHc1 _ _ _ _ _ _ _ _ _ _ _ commandProof commandProof0 memEq l_rel_pc1 l_not_pc1 l_rel_pc2 l_not_pc2));
        try (apply (IHc2 _ _ _ _ _ _ _ _ _ _ _ commandProof commandProof0 memEq l_rel_pc1 l_not_pc1 l_rel_pc2 l_not_pc2)).

  - pose proof (AlwaysLoopLengthDebranch p1); pose proof (AlwaysLoopLengthDebranch p2). destruct X; destruct X0. Check @MemStoreEquivalenceImplLoopLengthDebranchEq.
    pose proof (MemStoreEquivalenceImplLoopLengthDebranchEq IHc l_rel_pc1 l_not_pc1 l_rel_pc2 l_not_pc2 l0 l1 memEq); subst x1. clear p2; clear p1. revert memEq. generalize dependent mu2'. revert mu2. generalize dependent mu1'. revert mu1. dependent induction x0.
    + intros. dependent destruction l0; dependent destruction l1. assumption.
    + intros. dependent destruction l0; dependent destruction l1.

      
      pose proof (ExpressionLabelLowestBound expressionEvalProof lowProof); subst kl.
        pose proof (ExpressionLabelLowestBound expressionEvalProof0 lowProof0); subst kl0; clear lowProof lowProof0.    
        specialize (IHc _ _ _ _ _ _ _ _ _ _ _ commandProof commandProof0 memEq l_rel_pc1 l_not_pc1 l_rel_pc2 l_not_pc2).
        apply (IHx0 _ _ l0 _ _ l1 IHc).
Qed.
    

  
