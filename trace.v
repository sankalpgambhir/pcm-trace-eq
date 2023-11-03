Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

(* Assume we have a finite type `G` of generators. *)
Parameter G : Set.

(* Assume we have a special separator symbol `sep` *)
Parameter sep : G.

(* Assume we have a decidable equality on `G`. *)
Parameter G_eq_dec : forall x y : G, {x = y} + {x <> y}.

(* Define the commutation relation as a parameter. *)
Parameter commute : G -> G -> Prop.

(* We assume `commute` is symmetric and we should provide instances for it. *)
Axiom commute_sym : forall x y, commute x y -> commute y x.
Axiom commute_ref : forall x, commute x x.
Axiom commute_dec : forall x y, {commute x y} + {~commute x y}.

(* Define words in the partially commutative monoid as lists of `G`. *)
Definition word := list G.

(* The unit of the monoid is the empty list. *)
Definition unit : word := [].

(* commutative block encoding *)
Definition cbe := G -> list G.

Definition inc (l: list nat): list nat := 
    match l with
        | [] => []
        | head :: next => (S head) :: next
    end.

Fixpoint cb (w: word): cbe :=
    match w with
        | [] => fun _ => []
        | a :: next =>
            fun c => 
                if commute_dec a c then if G_eq_dec c a then c :: cb next c else cb next c else sep :: cb next c
    end.
Definition app_cbe (c1 c2: cbe) :=
    fun c => (c1 c) ++ (c2 c).

Lemma cb_add (w1 w2 : word): 
    cb (w1 ++ w2) = app_cbe (cb w1) (cb w2).
Proof.
    induction w1.
        unfold app_cbe.
        simpl.
        firstorder. (* why does firstorder work through lambdas though? *)

        apply functional_extensionality.
        intro c.
        change ((a :: w1) ++ w2) with (a :: (w1 ++ w2)).
        simpl cb at 1.
        simpl cb at 4.
        unfold app_cbe.
        destruct (commute_dec a c).
            destruct (G_eq_dec a c).
                rewrite e.
                destruct (G_eq_dec c c).
                rewrite IHw1.
                unfold app_cbe.
                auto.
                contradiction.
                destruct (G_eq_dec c a);
                    rewrite IHw1;
                    unfold app_cbe;
                    auto.
            rewrite IHw1.
            unfold app_cbe.
            auto.
Qed.

Lemma cbe_add_cancellation_tail (c1 c2 c3 : cbe):
    app_cbe c1 c2 = app_cbe c3 c2 <-> c1 = c3.
Proof.
    split.
        intro.
        apply functional_extensionality.
        intro.
        unfold app_cbe in H.
        enough (c1 x ++ c2 x = c3 x ++ c2 x).
            apply app_inv_tail in H0.
            assumption.

            change (c1 x ++ c2 x) with ((fun c => c1 c ++ c2 c) x).
            rewrite H.
            reflexivity.

        intro.
        rewrite H.
        reflexivity.
Qed.

Lemma cbe_add_cancellation_head (c1 c2 c3 : cbe):
    app_cbe c1 c2 = app_cbe c1 c3 <-> c2 = c3.
Proof.
    split.
        intro.
        apply functional_extensionality.
        intro.
        unfold app_cbe in H.
        enough (c1 x ++ c2 x = c1 x ++ c3 x).
            apply app_inv_head in H0.
            assumption.

            change (c1 x ++ c2 x) with ((fun c => c1 c ++ c2 c) x).
            rewrite H.
            reflexivity.

        intro.
        rewrite H.
        reflexivity.
Qed.

(* soundness base *)
Theorem cb_swap (w1 w2 : word) (a b : G):
    commute a b ->
        cb (w1 ++ [a; b] ++ w2) = cb (w1 ++ [b; a] ++ w2).
Proof.
    intros.
    repeat rewrite cb_add.
    apply cbe_add_cancellation_head.
    apply cbe_add_cancellation_tail.
    apply functional_extensionality.
    intro.
    unfold cb.
    destruct (commute_dec a x).
        destruct (G_eq_dec a x).
        destruct (G_eq_dec x a).
        rewrite e0.
        auto.
        destruct (commute_dec b a).
        destruct (commute_dec a b).
        destruct (G_eq_dec a b); auto.
        destruct (G_eq_dec a b); auto.
            apply commute_sym in H.
            contradiction.
        destruct (commute_dec b x); reflexivity.
        destruct (G_eq_dec x a).
        destruct (commute_dec b x).
        destruct (G_eq_dec x b); reflexivity. 
            rewrite e in n.
            contradiction.
        destruct (commute_dec b x); reflexivity.
        destruct (commute_dec b x).
        destruct (G_eq_dec x b).
            rewrite <- e in H.
            contradiction.
            reflexivity.
            reflexivity.
Qed.

(* correctness base *)
Theorem cb_dependent_swap (w1 w2 : word) (a b : G):
    ~commute a b -> 
    sep <> a -> sep <> b -> 
        cb (w1 ++ [a; b] ++ w2) <> cb (w1 ++ [b; a] ++ w2).
Proof.
    intros.
    unfold not. 
    intro.
    repeat rewrite cb_add in H2.
    apply cbe_add_cancellation_head in H2.
    apply cbe_add_cancellation_tail in H2.

    enough (cb [a; b] a <> cb [b; a] a).
        rewrite H2 in H3.
        contradiction.

        unfold not.
        intro.
        unfold cb in H3.

        (* back to cases *)
        destruct (commute_dec a a).
        destruct (G_eq_dec a a).
            destruct (commute_dec b a).
                apply commute_sym in c0.
                contradiction.
                inversion H3.
                auto.
            contradiction.
            assert (commute a a). exact (commute_ref a).
            contradiction.
Qed.     


