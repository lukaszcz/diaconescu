(*
Author: Lukasz Czajka

This file is in the public domain (no copyright).
*)

(* This is a readable Coq formalisation of two variants of
Diaconescu's theorem.

1. Predicate extensionality and the relativised axiom of choice
   together imply the excluded middle axiom.

2. Predicate extensionality and the axiom of choice together imply the
   excluded middle axiom.

The formalisation is based on the paper: N. Goodman, J. Myhill,
"Choice implies excluded middle", Zeitschrift für mathematische Logik
und Grundlagen der Mathematik 24:461 (1978)
 *)

(************************************************************************************)
(* Definitions *)

Definition AxiomOfChoice := forall (A B : Type) (R : A -> B -> Prop),
    (forall x : A, exists y : B, R x y) -> exists f : A -> B, forall x : A, R x (f x).

Definition RelativisedAxiomOfChoice :=
  forall (A B : Type) (Q : A -> Prop) (R : A -> B -> Prop),
    (forall x : A, Q x -> exists y : B, R x y) ->
    exists f : A -> B, forall x : A, Q x -> R x (f x).

Definition ExcludedMiddle := forall P : Prop, P \/ ~P.

Definition ProofIrrelevance := forall (P : Prop) (p q : P), p = q.

Definition PredicateExtensionality := forall (A : Type) (R1 R2 : A -> Prop),
    (forall x : A, R1 x <-> R2 x) -> R1 = R2.

Definition PropositionalExtensionality := forall (P Q : Prop), (P <-> Q) -> P = Q.

(************************************************************************************)
(* Diaconescu's theorem from relativised choice and predicate extensionality        *)

Theorem pre_diaconescu_rel :
  RelativisedAxiomOfChoice -> forall A (a b : A), a = b \/ a <> b.
Proof.
  unfold RelativisedAxiomOfChoice.
  intros Hc.
  intros A a b.
  pose (Q := fun x : A => x = a \/ x = b).
  pose (R := fun (x : A) (y : bool) => (x = a /\ y = true) \/ (x = b /\ y = false)).
  assert (H : exists f : A -> bool, forall x : A, Q x -> R x (f x)).
  { apply Hc.
    unfold Q, R.
    intros x H.
    destruct H; eauto. }
  destruct H as [f H].
  unfold Q, R in H.
  generalize (H a).
  generalize (H b).
  intros Ha Hb.
  destruct Ha as [[? Ha]|[? Ha]]; auto.
  destruct Hb as [[? Hb]|[? Hb]]; auto.
  right.
  intro.
  subst.
  rewrite Ha in Hb.
  discriminate Hb.
Qed.

Theorem diaconescu_rel :
  PredicateExtensionality -> RelativisedAxiomOfChoice -> ExcludedMiddle.
Proof.
  unfold PredicateExtensionality, RelativisedAxiomOfChoice, ExcludedMiddle.
  intros He Hc P.
  pose (U := fun x => x = true \/ P).
  pose (V := fun x => x = false \/ P).
  assert (H: U = V \/ U <> V) by auto using pre_diaconescu_rel.
  destruct H as [H|H].
  - left.
    assert (Heq: U false = V false) by congruence.
    unfold U, V in Heq.
    enough (H1: false = true \/ P) by
        (destruct H1 as [H1|?]; [ discriminate H1 | auto ]).
    rewrite Heq.
    auto.
  - right.
    intro HP.
    apply H.
    apply He.
    intro x.
    unfold U, V.
    split; auto.
Qed.

(************************************************************************************)
(* Diaconescu's theorem (non-relativised version) *)

Theorem pre_diaconescu : ProofIrrelevance -> AxiomOfChoice -> forall A (a b : A), a = b \/ a <> b.
Proof.
  unfold ProofIrrelevance, AxiomOfChoice.
  intros Hi Hc.
  intros A a b.
  pose (A' := {x : A | x = a \/ x = b}).
  pose (R := fun (x : A') (y : bool) => (proj1_sig x = a /\ y = true) \/ (proj1_sig x = b /\ y = false)).
  assert (H : exists f : A' -> bool, forall x : A', R x (f x)).
  { apply Hc.
    unfold R.
    intro x.
    destruct x as [x H].
    simpl.
    destruct H; subst; eauto. }
  destruct H as [f H].
  unfold R in H.
  generalize (H ltac:(unfold A'; exists a; auto)).
  generalize (H ltac:(unfold A'; exists b; auto)).
  simpl.
  intros Ha Hb.
  destruct Ha as [[? Ha]|[? Ha]]; auto.
  destruct Hb as [[? Hb]|[? Hb]]; auto.
  right.
  intro; subst.
  assert (He: or_introl eq_refl = or_intror eq_refl :> (b = b \/ b = b)) by auto.
  rewrite He in Hb.
  rewrite Hb in Ha.
  discriminate Ha.
Qed.

Lemma lem_pred_to_prop : PredicateExtensionality -> PropositionalExtensionality.
Proof.
  unfold PredicateExtensionality, PropositionalExtensionality.
  intros H P Q H1.
  generalize (H bool (fun _ => P) (fun _ => Q)).
  intro H2.
  generalize (H2 (fun _ => H1)).
  intro H3.
  change ((fun _ => P) true = (fun _ => Q) true).
  rewrite H3.
  reflexivity.
Qed.

Lemma lem_prop_to_irrelev : PropositionalExtensionality -> ProofIrrelevance.
Proof.
  unfold PropositionalExtensionality, ProofIrrelevance.
  intros H P p q.
  unfold iff in H.
  assert (H1: P = True) by auto.
  subst.
  destruct p, q.
  reflexivity.
Qed.

Theorem diaconescu : PredicateExtensionality -> AxiomOfChoice -> ExcludedMiddle.
Proof.
  unfold PredicateExtensionality, AxiomOfChoice, ExcludedMiddle.
  intros He Hc P.
  pose (U := fun x => x = true \/ P).
  pose (V := fun x => x = false \/ P).
  assert (H: U = V \/ U <> V) by
      eauto using pre_diaconescu, lem_pred_to_prop, lem_prop_to_irrelev.
  destruct H as [H|H].
  - assert (Heq: U false = V false) by congruence.
    unfold U, V in Heq.
    enough (HH: false = true \/ P)
      by (destruct HH; [ easy | auto ]).
    rewrite Heq.
    auto.
  - enough (~P) by auto.
    intro H1.
    apply H.
    apply He.
    unfold U, V.
    tauto.
Qed.
