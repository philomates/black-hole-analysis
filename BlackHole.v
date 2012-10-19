Require Export Defs.
Require Export SfLib.

Module STLCHoles.

(* ###################################################################### *)
(** *** Syntax and Operational Semantics *)

Inductive ty : Type :=
  | ty_arrow : ty -> ty -> ty
  | ty_bool  : ty
  | ty_nat   : ty
  | ty_hole  : ty -> ty.

Tactic Notation "ty_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ty_arrow" | Case_aux c "ty_bool"
  | Case_aux c "ty_nat"   | Case_aux c "ty_hole"].

Inductive tm : Type :=
  (* pure STLC *)
  | tm_var : id -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : id -> ty -> tm -> tm
  (* numbers *)
  | tm_nat : nat -> tm
  | tm_mult : tm -> tm -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  (* bools *)
  | tm_if  : tm -> tm -> tm -> tm
  | tm_tt : tm
  | tm_ff : tm
  (* holes *)
  | tm_hole : ty -> tm.

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tm_var" | Case_aux c "tm_app" | Case_aux c "tm_abs"
  | Case_aux c "tm_nat" | Case_aux c "tm_mult" | Case_aux c "tm_succ"
  | Case_aux c "tm_pred" | Case_aux c "tm_if" | Case_aux c "tm_tt"
  | Case_aux c "tm_ff" | Case_aux c "tm_hole" ].

(* ###################################################################### *)
(** *** Substitution *)

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tm_var y => 
      if beq_id x y then s else t
  | tm_abs y T t1 => 
      tm_abs y T (if beq_id x y then t1 else (subst x s t1))
  | tm_app t1 t2 => 
      tm_app (subst x s t1) (subst x s t2)
  | tm_nat n => t
  | tm_succ t1 =>
      tm_succ (subst x s t1)
  | tm_pred t1 =>
      tm_pred (subst x s t1)
  | tm_mult t1 t2 =>
      tm_mult (subst x s t1) (subst x s t2)
  | tm_if t1 t2 t3 =>
      tm_if (subst x s t1) (subst x s t2) (subst x s t3)
  | tm_tt => tm_tt
  | tm_ff => tm_ff
  | tm_hole T => tm_hole T
  end.

(* ###################################################################### *)
(** *** Reduction *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (tm_abs x T11 t12)
  | v_nat : forall x,
      value (tm_nat x)
  | v_tt : 
      value tm_tt
  | v_ff : 
      value tm_ff
  | v_hole : forall T,
      value (tm_hole T).

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T11 t12 v2,
      value v2 ->
      (tm_app (tm_abs x T11 t12) v2) ==> (subst x v2 t12)
  | ST_App1 : forall t1 t1' t2,
      t1 ==> t1' ->
      (tm_app t1 t2) ==> (tm_app t1' t2)
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      (tm_app v1 t2) ==> (tm_app v1 t2')
  | ST_If : forall b b' x y,
      b ==> b' ->
      (tm_if b x y) ==> (tm_if b' x y)
  | ST_IfTrue : forall x y,
      (tm_if tm_tt x y) ==> x
  | ST_IfFalse : forall x y,
      (tm_if tm_ff x y) ==> y
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tm_succ t1) ==> (tm_succ t1')
  | ST_Succ1 : forall n,
      (tm_succ (tm_nat n)) ==> (tm_nat (plus 1 n))
  | ST_PredSucc : forall t1,
      (tm_pred (tm_succ t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tm_pred t1) ==> (tm_pred t1')
  | ST_Pred2 : forall n,
      (tm_pred (tm_nat n)) ==> (tm_nat (pred n))
  | ST_PredZero : 
      (tm_pred (tm_nat 0)) ==> (tm_nat 0)
  | ST_Mult1 : forall x x' y,
      x ==> x' ->
      (tm_mult x y) ==> (tm_mult x' y)
  | ST_Mult2 : forall x y y',
      y ==> y' ->
      (tm_mult x y) ==> (tm_mult x y')
  | ST_Mult3 : forall x y,
      (tm_mult (tm_nat x) (tm_nat y)) ==> (tm_nat (mult x y))
  (* Hole reductions *)
  | ST_AppH : forall v T1 T2,
      tm_app (tm_hole (ty_arrow T1 T2)) v ==> tm_hole T2
  | ST_AppAbsH : forall x t T1,
      tm_app (tm_abs x T1 t) (tm_hole T1) ==> (subst x (tm_hole T1) t)
  | ST_IfH1 : forall e1 e2,
      tm_if (tm_hole ty_bool) e1 e2 ==> e1
  | ST_IfH2 : forall e1 e2,
      tm_if (tm_hole ty_bool) e1 e2 ==> e2
  | ST_MultH1 : forall n1,
      tm_mult (tm_hole ty_nat) n1 ==> (tm_hole ty_nat)
  | ST_MultH2 : forall n1,
      tm_mult n1 (tm_hole ty_nat) ==> (tm_hole ty_nat)
  | ST_SuccH : 
      tm_succ (tm_hole ty_nat) ==> tm_hole ty_nat
  | ST_PredH : 
      tm_pred (tm_hole ty_nat) ==> tm_hole ty_nat

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" | Case_aux c "ST_App2"
  | Case_aux c "ST_If" | Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse"
  | Case_aux c "ST_Succ" | Case_aux c "ST_Succ1" | Case_aux c "ST_PredSucc"
  | Case_aux c "ST_Pred" | Case_aux c "ST_Pred2" | Case_aux c "ST_PredZero" 
  | Case_aux c "ST_Mult1" | Case_aux c "ST_Mult2" | Case_aux c "ST_Mult3"
  | Case_aux c "ST_AppH" | Case_aux c "ST_AppAbsH" | Case_aux c "ST_IfH1"
  | Case_aux c "ST_IfH2" | Case_aux c "ST_MultH1" | Case_aux c "ST_MultH2"
  | Case_aux c "ST_SuccH" | Case_aux c "ST_PredH" ].

Notation stepmany := (refl_step_closure step).
Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

Hint Constructors step.

(* ###################################################################### *)
(** *** Typing *)

Definition context := partial_map ty.

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Typing rules for proper terms *)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      has_type Gamma (tm_var x) T
  | T_Abs : forall Gamma x T11 T12 t12,
      has_type (extend Gamma x T11) t12 T12 -> 
      has_type Gamma (tm_abs x T11 t12) (ty_arrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      has_type Gamma t1 (ty_arrow T1 T2) -> 
      has_type Gamma t2 T1 -> 
      has_type Gamma (tm_app t1 t2) T2
  | T_Nat : forall Gamma n,
      has_type Gamma (tm_nat n) ty_nat
  | T_Mult : forall Gamma n m,
      has_type Gamma n ty_nat ->
      has_type Gamma m ty_nat ->
      has_type Gamma (tm_mult n m) ty_nat
  | T_Succ : forall Gamma n,
      has_type Gamma n ty_nat ->
      has_type Gamma (tm_succ n) ty_nat
  | T_Pred : forall Gamma n,
      has_type Gamma n ty_nat ->
      has_type Gamma (tm_pred n) ty_nat  
  | T_True : forall Gamma,
      has_type Gamma tm_tt ty_bool
  | T_False : forall Gamma,
      has_type Gamma tm_ff ty_bool
  | T_If : forall Gamma b x y T,
      has_type Gamma b ty_bool ->
      has_type Gamma x T ->
      has_type Gamma y T ->
      has_type Gamma (tm_if b x y) T
  | T_Hole : forall Gamma T,
      has_type Gamma (tm_hole T) T.

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App" 
  | Case_aux c "T_Nat"  | Case_aux c "T_Mult" | Case_aux c "T_Succ" 
  | Case_aux c "T_Pred" | Case_aux c "T_True" | Case_aux c "T_False"
  | Case_aux c "T_If" | Case_aux c "T_Hole" ].

(* ------------------------------------------------------ *)
(** Refinement relation **)

Inductive Refines : context -> tm -> tm -> ty -> Prop :=
    R_base : forall Gamma e T,
      has_type Gamma e T ->
      Refines Gamma e (tm_hole T) T
(*  | R_trans : forall Gamma e1 e2 e3 T, 
      Refines Gamma e1 e2 T ->
      Refines Gamma e2 e3 T ->
      Refines Gamma e1 e3 T *)
  | R_refl : forall Gamma e T,
      has_type Gamma e T ->
      Refines Gamma e e T
  | R_if : forall Gamma b b' e1 e1' e2 e2' T,
      Refines Gamma b b' ty_bool ->
      Refines Gamma e1 e1' T ->
      Refines Gamma e2 e2' T ->
      Refines Gamma (tm_if b e1 e2) (tm_if b' e1' e2') T
  | R_app : forall Gamma e1 e1' e2 e2' T1 T2,
      Refines Gamma e1 e1' (ty_arrow T1 T2) ->
      Refines Gamma e2 e2' T1 ->
      Refines Gamma (tm_app e1 e2) (tm_app e1' e2') T2
  | R_abs : forall Gamma e1 e1' x T1 T2,
      Refines (extend Gamma x T1) e1 e1' T2 ->
      Refines Gamma (tm_abs x T1 e1) (tm_abs x T1 e1') (ty_arrow T1 T2)
  | R_mult : forall Gamma e1 e1' e2 e2',
      Refines Gamma e1 e1' ty_nat ->
      Refines Gamma e2 e2' ty_nat ->
      Refines Gamma (tm_mult e1 e2) (tm_mult e1' e2') ty_nat.
Tactic Notation "refines_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "R_base" | (* Case_aux c "R_trans" | *) Case_aux c "R_refl" 
  | Case_aux c "R_if" | Case_aux c "R_app" | Case_aux c "R_abs"
  | Case_aux c "R_mult" ].



(* ###################################################################### *)
(** ** Properties of Typing *)

(** The proofs of progress and preservation for this system are
    essentially the same (though of course somewhat longer) as for the
    pure simply typed lambda-calculus. *)

(* ###################################################################### *)
(** *** Progress *)

Theorem progress : forall t T, 
     has_type empty t T ->
     value t \/ exists t', t ==> t'. 
Proof with eauto.
  (* Theorem: Suppose empty |- t : T.  Then either
       1. t is a value, or
       2. t ==> t' for some t'.
     Proof: By induction on the given typing derivation. *)
  intros t T Ht.
  remember (@empty ty) as Gamma.
  generalize dependent HeqGamma.
  has_type_cases (induction Ht) Case; intros HeqGamma; subst.
  Case "T_Var".
    (* The final rule in the given typing derivation cannot be [T_Var],
       since it can never be the case that [empty |- x : T] (since the
       context is empty). *)
    inversion H.
  Case "T_Abs".
    (* If the [T_Abs] rule was the last used, then [t = tm_abs x T11 t12],
       which is a value. *)
    left...
  Case "T_App".
    (* If the last rule applied was T_App, then [t = t1 t2], and we know 
       from the form of the rule that
         [empty |- t1 : T1 -> T2]
         [empty |- t2 : T1]
       By the induction hypothesis, each of t1 and t2 either is a value 
       or can take a step. *)
    right.
    destruct IHHt1; subst...
    SCase "t1 is a value".
      destruct IHHt2; subst...
      SSCase "t2 is a value".
      (* If both [t1] and [t2] are values, then we know that 
         [t1 = tm_abs x T11 t12], since abstractions are the only values
         that can have an arrow type.  But 
         [(tm_abs x T11 t12) t2 ==> subst x t2 t12] by [ST_AppAbs]. *)
        inversion H; subst; try (solve by inversion).
        exists (subst x t2 t12)...
        inversion Ht1. subst.
        exists (tm_hole T2). apply ST_AppH.
      SSCase "t2 steps".
        (* If [t1] is a value and [t2 ==> t2'], then [t1 t2 ==> t1 t2'] 
           by [ST_App2]. *)
        destruct H0 as [t2' Hstp]. exists (tm_app t1 t2')...
    SCase "t1 steps".
      (* Finally, If [t1 ==> t1'], then [t1 t2 ==> t1' t2] by [ST_App1]. *)
      destruct H as [t1' Hstp]. exists (tm_app t1' t2)...
  Case "T_Nat".
    left...
  Case "T_Mult".
    right.
    destruct IHHt1; subst...
    SCase "t1 is a value".
      destruct IHHt2; subst...
      SSCase "t2 is a value".
        inversion H; subst; try (solve by inversion).
        inversion H0; subst; try (solve by inversion).
  
        exists (tm_nat (mult x x0)). auto.
        inversion Ht2; subst.
        exists (tm_hole ty_nat). apply ST_MultH2.
        inversion Ht1; subst.
        exists (tm_hole ty_nat). apply ST_MultH1.
      SSCase "t2 steps".
        inversion H0 as [m' Hstp].
        exists (tm_mult n m')...
    SCase "t1 steps".
        inversion H as [n' Hstp].
        exists (tm_mult n' m)...
  Case "T_Succ".
    right.
    destruct IHHt; subst...
    inversion H; subst; try (solve by inversion).
    exists (tm_nat (plus 1 x)). auto.
    inversion Ht; subst.
    exists (tm_hole ty_nat). apply ST_SuccH.
    destruct H as [n' Hstp]...
  Case "T_Pred".
    right.
    destruct IHHt; subst...
    inversion H; subst; try (solve by inversion).
    exists (tm_nat (pred x)). auto.
    inversion Ht; subst.
    exists (tm_hole ty_nat). apply ST_PredH.
    destruct H as [n' Hstp]...
  Case "T_True".    
    left...
  Case "T_False".    
    left...
  Case "T_If".
    admit.
  Case "T_Hole".
    left...
Qed.


(* ###################################################################### *)
(** *** Context Invariance *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tm_var x)
  | afi_succ : forall x n,
      appears_free_in x n ->
      appears_free_in x (tm_succ n)
  | afi_pred : forall x n,
      appears_free_in x n ->
      appears_free_in x (tm_pred n)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x  ->
      appears_free_in x t12 ->
      appears_free_in x (tm_abs y T11 t12)
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tm_if t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tm_if t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tm_if t1 t2 t3)
  | afi_mult2 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tm_mult t1 t2)
  | afi_mult1 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tm_mult t1 t2)
  .

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
     has_type Gamma t S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     has_type Gamma' t S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  has_type_cases (induction H) Case; 
    intros Gamma' Heqv...
    Case "T_Var".
      apply T_Var... rewrite <- Heqv...
    Case "T_Abs".
      apply T_Abs... apply IHhas_type. intros y Hafi.
      unfold extend. remember (beq_id x y) as e.
      destruct e... apply Heqv. apply afi_abs.
      apply beq_id_false_not_eq. symmetry. assumption.
      assumption.
    Case "T_App".
      apply T_App with T1...
    Case "T_Mult".
      apply T_Mult...
    Case "T_If".
      apply T_If...
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   has_type Gamma t T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  has_type_cases (induction Htyp) Case; inversion Hafi; subst...
  Case "T_Abs".
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold extend in Hctx. 
    apply not_eq_beq_id_false in H2. rewrite H2 in Hctx...
Qed.

(* ###################################################################### *)
(** *** Preservation *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     has_type (extend Gamma x U) t S  ->
     has_type empty v U   ->
     has_type Gamma (subst x v t) S.
Proof with eauto.
  (* Theorem: If Gamma,x:U |- t : S and empty |- v : U, then 
     Gamma |- (subst x v t) S. *)
  intros Gamma x U v t S Htypt Htypv. 
  generalize dependent Gamma. generalize dependent S.
  (* Proof: By induction on the term t.  Most cases follow directly
     from the IH, with the exception of tm_var and tm_abs.
     The former aren't automatic because we must reason about how the
     variables interact. *)
  tm_cases (induction t) Case;
    intros S Gamma Htypt; simpl; inversion Htypt; subst...
  Case "tm_var".
    simpl. rename i into y.
    (* If t = y, we know that
         [empty |- v : U] and
         [Gamma,x:U |- y : S]
       and, by inversion, [extend Gamma x U y = Some S].  We want to
       show that [Gamma |- subst x v y : S].

       There are two cases to consider: either [x=y] or [x<>y]. *)
    remember (beq_id x y) as e. destruct e.
    SCase "x=y".
    (* If [x = y], then we know that [U = S], and that [subst x v y = v].
       So what we really must show is that if [empty |- v : U] then
       [Gamma |- v : U].  We have already proven a more general version
       of this theorem, called context invariance. *)
      apply beq_id_eq in Heqe. subst.
      unfold extend in H1. rewrite <- beq_id_refl in H1. 
      inversion H1; subst. clear H1.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
    (* If [x <> y], then [Gamma y = Some S] and the substitution has no
       effect.  We can show that [Gamma |- y : S] by [T_Var]. *)
      apply T_Var... unfold extend in H1. rewrite <- Heqe in H1...
  Case "tm_abs".
    rename i into y. rename t into T11.
    (* If [t = tm_abs y T11 t0], then we know that
         [Gamma,x:U |- tm_abs y T11 t0 : T11->T12]
         [Gamma,x:U,y:T11 |- t0 : T12]
         [empty |- v : U]
       As our IH, we know that forall S Gamma, 
         [Gamma,x:U |- t0 : S -> Gamma |- subst x v t0 S].
    
       We can calculate that 
         subst x v t = tm_abs y T11 (if beq_id x y
                                      then t0 
                                      else subst x v t0)
       And we must show that [Gamma |- subst x v t : T11->T12].  We know
       we will do so using [T_Abs], so it remains to be shown that:
         [Gamma,y:T11 |- if beq_id x y then t0 else subst x v t0 : T12]
       We consider two cases: [x = y] and [x <> y].
    *)
    apply T_Abs...
    remember (beq_id x y) as e. destruct e.
    SCase "x=y".
    (* If [x = y], then the substitution has no effect.  Context
       invariance shows that [Gamma,y:U,y:T11] and [Gamma,y:T11] are
       equivalent.  Since the former context shows that [t0 : T12], so
       does the latter. *)
      eapply context_invariance...
      apply beq_id_eq in Heqe. subst.
      intros x Hafi. unfold extend.
      destruct (beq_id y x)...
    SCase "x<>y".
    (* If [x <> y], then the IH and context invariance allow us to show that
         [Gamma,x:U,y:T11 |- t0 : T12]       =>
         [Gamma,y:T11,x:U |- t0 : T12]       =>
         [Gamma,y:T11 |- subst x v t0 : T12] *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      remember (beq_id y z) as e0. destruct e0...
      apply beq_id_eq in Heqe0. subst.
      rewrite <- Heqe...
Qed.

Theorem preservation : forall t t' T,
     has_type empty t T  ->
     t ==> t'  ->
     has_type empty t' T.
Proof with eauto.
  intros t t' T HT.
  (* Theorem: If [empty |- t : T] and [t ==> t'], then [empty |- t' : T]. *)
  remember (@empty ty) as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  (* Proof: By induction on the given typing derivation.  Many cases are
     contradictory ([T_Var], [T_Abs]).  We show just the interesting ones. *)
  has_type_cases (induction HT) Case; 
    intros t' HeqGamma HE; subst; inversion HE; subst...
  Case "T_App".
    (* If the last rule used was [T_App], then [t = t1 t2], and three rules
       could have been used to show [t ==> t']: [ST_App1], [ST_App2], and 
       [ST_AppAbs]. In the first two cases, the result follows directly from 
       the IH. *)
    inversion HE; subst...
    SCase "ST_AppAbs".
      (* For the third case, suppose 
           [t1 = tm_abs x T11 t12]
         and
           [t2 = v2].  
         We must show that [empty |- subst x v2 t12 : T2]. 
         We know by assumption that
             [empty |- tm_abs x T11 t12 : T1->T2]
         and by inversion
             [x:T1 |- t12 : T2]
         We have already proven that substitution_preserves_typing and 
             [empty |- v2 : T1]
         by assumption, so we are done. *)
      apply substitution_preserves_typing with T1...
      inversion HT1...
    SCase "ST_AppAbsH".
      apply substitution_preserves_typing with T11.
      inversion HT1...
      apply T_Hole.
    SCase "ST_AppH".
      inversion HT1; subst...
    SCase "ST_AppAbsH??".
      apply substitution_preserves_typing with T1. 
      inversion HT1... auto.
  Case "T_Pred". 
    inversion HT; subst. assumption.
Qed.



(** Proofs **)

Theorem refinement_implies_welltypedness : forall Gamma v u T,
  Refines Gamma v u T ->
  has_type Gamma v T.
Proof with eato.
  intros.
  refines_cases (induction H) Case; try (assumption).
  Case "R_if".
    apply T_If.
    assumption. assumption. assumption. 
  Case "R_app".
    eapply T_App. apply IHRefines1. apply IHRefines2.
  Case "R_abs".
    eapply T_Abs. apply IHRefines.
  Case "R_mult".
    apply T_Mult. assumption. assumption.
Qed.

Theorem extension_aliasing : forall Gamma x y z (T1:ty) (T2:ty),
  beq_id x y = true ->
  (extend (extend Gamma x T1) y T2) z = (extend Gamma y T2) z.
Proof.
  intros.
  unfold extend.
  assert (x=y). apply beq_id_eq. symmetry. assumption.
  rewrite <- H0.
  remember (beq_id x z) as E.
  destruct (beq_id x z). rewrite -> HeqE. reflexivity.

  rewrite -> HeqE.
  reflexivity.
Qed.

Theorem substitution_lemma : forall Gamma v u x Tx e1 e2 Te,
  Refines (extend Gamma x Tx) e1 e2 Te ->
  Refines empty v u Tx ->
  Refines Gamma (subst x v e1) (subst x u e2) Te.
Proof with eauto.
  intros Gamma v u x Tx e1 e2 Te H.

  remember (extend Gamma x Tx) as GammaX. 
  (* generalize dependent Tx. *)

  refines_cases (induction H) Case; intros.
  Case "R_base".
    simpl. apply R_base. apply substitution_preserves_typing with (U:= Tx).
    rewrite -> HeqGammaX in H. assumption.

    eapply refinement_implies_welltypedness. apply H0.
  Case "R_refl".
    rewrite -> HeqGammaX in H.

    tm_cases (induction H) SCase.
    SCase "tm_var".
      unfold subst. remember (beq_id x x0) as e. destruct e.
      SSCase "x=x0".
        admit. (* fix empty/Gamma problem... *)
      SSCase "x<>x0".
        apply R_refl. apply T_Var.
        rewrite <- HeqGammaX in H.
        admit.
        (* rewrite -> extend_neq in H. apply H. symmetry. apply Heqe. *)
    SCase "tm_app".
      remember (beq_id x x0) as e.
      destruct e.
      SSCase "x = x0".
        simpl. rewrite <- Heqe.
        apply R_refl.
        admit.
        (*
        apply T_Abs. rewrite -> HeqGammaX in H.
        assert (x = x0) as xEq. apply beq_id_eq. assumption.
        rewrite -> xEq in H.
        assert ((extend Gamma x0 T11) = (extend (extend Gamma x0 Tx) x T11)).
        admit.
        (* fix to give Gamma an argument so that the shadowing lemma can be used *)
        admit. 
*)
      
      SSCase "x <> x0".
        simpl. rewrite <- Heqe.
        apply R_abs. 
        admit.
    SCase "tm_abs".
      admit.
    SCase "tm_nat".
      admit.
    SCase "tm_mult".
      admit.
    SCase "tm_succ".
      admit.
    SCase "tm_pred".  
      admit.
    SCase "tm_if".
      admit.
    SCase "tm_tt".
      admit.
    SCase "tm_ff".
      admit.
    SCase "tm_hole".
      admit.
  Case "R_if".
    simpl. apply R_if... 
  Case "R_app".
    simpl. apply R_app with (T1:=T1)...
  Case "R_abs".
    simpl. remember (beq_id x x0) as b.
    destruct b.
    SCase "x == x0".
      apply R_abs...
      rewrite -> HeqGammaX in H.
      assert ((extend (extend Gamma x Tx) x0 T1) = (extend Gamma x0 T1)).
      (* apply extension_aliasing with (x:=x T1:=Tx y:=x0 T1:=T2). *)
      admit.
      rewrite -> H1 in H.
      apply H.
    SCase "x <> x0".
      apply R_abs...
      (* stuck... *)
      admit.
  Case "R_mult".
    simpl. apply R_mult...
Qed.

Theorem transitivity_of_refines : forall Gamma a b c T,
  Refines Gamma a b T ->
  Refines Gamma b c T ->
  Refines Gamma a c T.
Proof with eauto.
  intros Gamma a b c T Hab Hbc.
  refines_cases (induction Hab) Case.
  Case "R_base".
    inversion Hbc; subst.
    apply R_base...
    apply R_base...
  Case "R_refl".
    inversion Hbc; subst...
  Case "R_if".
    inversion Hbc; subst...
    apply R_base...
    apply T_If.
    eapply refinement_implies_welltypedness. apply Hab1.
    eapply refinement_implies_welltypedness. apply Hab2.
    eapply refinement_implies_welltypedness. apply Hab3.

    eapply R_if...
    admit.
  Case "R_app".
    inversion Hbc; subst.
    SCase "tm_hole".
     apply R_base. 
     eapply T_App.
     eapply refinement_implies_welltypedness. apply Hab1.
     eapply refinement_implies_welltypedness. apply Hab2.
    SCase "tm_app".
     eapply R_app...

   admit.

  Case "R_abs".
    inversion Hbc; subst.
    SCase "tm_hole".
      apply R_base...
      apply T_Abs. eapply refinement_implies_welltypedness. apply Hab.
    SCase "tm_abs".
      apply R_abs...
    admit.

  Case "R_mult".    
    inversion Hbc; subst.
    SCase "tm_hole".
      apply R_base.
      eapply T_Mult.
        eapply refinement_implies_welltypedness. apply Hab1.
        eapply refinement_implies_welltypedness. apply Hab2.
    SCase "tm_mult".
      apply R_mult...
    admit.
Qed.


Theorem soundness : forall Gamma p q p' T,
  Refines Gamma p q T -> 
  p ==> p' -> 
  exists q', q ==>* q' /\
  Refines Gamma p' q' T.
Proof.
  intros Gamma p q p' T H S.
  step_cases (induction S) Case.
  Case "ST_AppAbs".
    inversion H; subst.
    exists (tm_hole T).
    split. apply rsc_refl.
    apply R_base.
    inversion H1; subst.
    eapply substitution_preserves_typing with (U:=T1).
    inversion H5; subst. 
    assumption. admit.

    exists (subst x v2 t12).
    split. eapply rsc_step. eapply ST_AppAbs. assumption. apply rsc_refl.
    eapply substitution_lemma.
    eapply R_refl.
    inversion H1; subst. inversion H5; subst. apply H4.
    eapply R_refl. inversion H1; subst. inversion H5; subst. admit.
    exists v2.
    split.
Admitted.
