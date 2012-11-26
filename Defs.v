Require Export SfLib.

Definition relation (X: Type) := X->X->Prop.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

(** * Reflexive, Transitive Closure *)

(** The _reflexive, transitive closure_ of a relation [R] is the
    smallest relation that contains [R] and that is both reflexive and
    transitive.  Formally, it is defined like this in the Relations
    module of the Coq standard library: *)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y ->
          clos_refl_trans R y z ->
          clos_refl_trans R x z.

Tactic Notation "rt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rt_step" | Case_aux c "rt_refl" 
  | Case_aux c "rt_trans" ].


Inductive refl_step_closure {X:Type} (R: relation X) : relation X :=
  | rsc_refl  : forall (x : X), refl_step_closure R x x
  | rsc_step : forall (x y z : X),
                    R x y ->
                    refl_step_closure R y z ->
                    refl_step_closure R x z.
Hint Constructors refl_step_closure.

Tactic Notation "rsc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rsc_refl" | Case_aux c "rsc_step" ].

Theorem rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> (refl_step_closure R) x y.
Proof.
  intros X R x y H.
  apply rsc_step with y. apply H. apply rsc_refl. Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Definition normalizing {X:Type} (R:relation X) :=
  forall t, exists t',
    (refl_step_closure R) t t' /\ normal_form R t'.


Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if beq_id x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite <- beq_id_refl. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  beq_id x2 x1 = false ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite H. auto.
Qed.

Hint Unfold beq_id beq_nat extend.
