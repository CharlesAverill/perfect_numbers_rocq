From Coq Require Import ssreflect ssrfun ssrbool Zify.
From mathcomp Require Import eqtype ssrnat div prime zify.

Lemma eq_eqb_same_mod : forall a b m,
    (a = b %[mod m]) <-> (a == b %[mod m]).
Proof.
    intros. split; intro.
    {
        intros. pose proof eqP (x := a %% m) (y := b %% m).
        inversion H0. reflexivity. contradiction.
    } {
        intros. pose proof eqP (x := a %% m) (y := b %% m).
        inversion H0. assumption. rewrite H in H1. inversion H1.
    }
Qed.

Lemma subn_0_r : forall n,
    n - 0 = n.
Proof. lia. Qed.

Lemma pow2n_1_modsub1 : forall n,
    0 < n ->
    2^n == 1 %[mod 2^n - 1].
Proof.
    intros. replace (2^n) with ((2^n - 1) + 1) at 1 by lia.
    rewrite addnC.
    apply eq_eqb_same_mod.
    rewrite modnDr. lia.
Qed.

Lemma modnM : forall a b c d m,
    b <= a -> d <= c ->
    a == b %[mod m] ->
    c == d %[mod m] ->
    a * c == b * d %[mod m].
Proof.
    intros.
    rewrite eqn_mod_dvd in H1.
    rewrite eqn_mod_dvd in H2.
    pose proof (dvdnP H1). pose proof (dvdnP H2).
    destruct H3 as (k & H3), H4 as (l & H4).
    pose proof (f_equal (muln c) H3).
    pose proof (f_equal (muln b) H4).
    assert (a * c = b * c %[mod m]). {
        apply eq_eqb_same_mod.
        rewrite eqn_mod_dvd.
        rewrite mulnBr in H5.
        rewrite mulnC (mulnC b c) H5 (mulnC k m) mulnC -mulnA.
        replace m with (m * 1) at 1 by lia.
        rewrite dvdn_mul => //.
        apply leq_mul; lia.
    } assert (c * b = d * b %[mod m]). {
        apply eq_eqb_same_mod.
        rewrite eqn_mod_dvd.
        rewrite mulnBr in H6.
        rewrite mulnC (mulnC d b) H6 (mulnC l m) mulnC -mulnA.
        replace m with (m * 1) at 1 by lia.
        rewrite dvdn_mul => //.
        apply leq_mul; lia.
    } rewrite H7 mulnC (mulnC b d) H8. apply eq_refl.
    assumption.
    assumption.
Qed.

Lemma pow_under_mod : forall k a b m,
    0 < k ->
    b <= a ->
    a == b %[mod m] -> a^k == b^k %[mod m].
Proof.
    destruct k.
        intros. inversion H.
    induction k; intros.
        by rewrite expn1 expn1.
    rewrite (expnS a) (expnS b).
    assert (0 < k.+1) by lia.
    specialize (IHk _ _ _ H2 H0 H1).
    apply modnM => //.
    by rewrite leq_exp2r.
Qed.

Lemma eq_refl_mod : forall n k,
    n = n %[mod k].
Proof. lia. Qed.

Lemma add_bs_mod : forall k x m,
    k <= x ->
    x == k %[mod m] -> x - k == 0 %[mod m].
Proof.
    intros.
    rewrite eqn_mod_dvd in H0.
    rewrite eqn_mod_dvd. rewrite subn_0_r => //.
        constructor.
    auto.
Qed.

(* n is the index of a mersenne prime *)
Definition mp (n : nat) : Prop :=
    prime (2^n - 1).
#[global] Hint Unfold mp : core.

Example mersenne_prime_31 : mp 5.
Proof. auto. Qed.

(* A mersenne prime's index must be prime *)
Lemma mp_n_impl_prime_n : forall n,
    mp n -> prime n.
Proof.
    intros. unfold mp in H.
    assert (0 < n) by induction n => //.
    (* Case analysis on primality of n, true is trivial *)
    destruct (prime n) eqn:E => //.
    assert (~~ prime n) by by rewrite E. clear E.
    (* either n is less than 2 or it has a factor between 1 and n *)
    pose proof (primePn H1).
    destruct H2.
    (* n < 2 *)
    destruct n. inversion H0. rewrite <- ltn_predRL in H2.
        simpl in H2. replace n with 0 in *.
        inversion H. destruct n => //.
    (* n has a factor between 1 and n *)
    destruct H2.
    (* if n has a factor, then 2^n - 1 must also have a factor *)
    assert (exists k, 1 < k < 2^n - 1 /\ k %| 2^n - 1). {
        exists (2^x - 1). apply andb_prop in H2. destruct H2. 
        assert (2^x - 1 < 2^n - 1). {
            rewrite ltn_sub2rE. rewrite ltn_exp2l => //.
            apply expn_gt0.
        } split.
        rewrite H5 Bool.andb_true_r. destruct x.
            inversion H2. destruct x. inversion H2.
            change (x.+2) with (2 + x). rewrite expnD.
            change (2^2) with 4. clear. lia.
        (* We know that 2^x = 1 (mod 2^x - 1) *)
        pose proof (pow2n_1_modsub1 x ltac:(lia)).
        assert (2^n - 1 == 0 %[mod 2^x - 1]). {
            apply pow_under_mod with (k := n%/x) in H6.
            rewrite exp1n in H6.
            replace ((2^x)^(n%/x)) with (2^n) in H6.
            rewrite add_bs_mod => //. lia.
            rewrite <- expnM. rewrite muln_divA => //.
            rewrite mulKn => //. lia. destruct x.
                inversion H2.
            lia. lia.
        }
        (* Now show that 2^x -1 divides 2^n - 1 by the above subproof *)
        rewrite eqn_mod_dvd in H7.
        by rewrite subn_0_r in H7. constructor.
    } destruct H4 as (k & H5 & H6).
    (* If 2^n - 1 has a factor, we have a contradiction because 
       by the original theorem statement, we have assumed that
       2^n - 1 is prime
    *) 
    pose proof (primeP H). destruct H4.
    specialize (H7 _ H6). apply Bool.orb_prop in H7. destruct H7.
        pose proof (eqP H7). subst.
        inversion H5.
    pose proof (eqP H7). subst.
    rewrite ltnn in H5. rewrite Bool.andb_false_r in H5. inversion H5.
Qed.


