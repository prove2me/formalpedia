-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.iInf_pow_eq_pow_iInf_of_pairwise_sup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T21:14:02.8631+00:00
-- url     : https://prove2.me/submissions/3d24b97c-000d-4b0f-bad0-2ab8648bb165

import Mathlib.RingTheory.Ideal.Operations

theorem solution
    {R : Type*} [CommSemiring R] (K : ℕ) (I : Fin K → Ideal R) (n : ℕ)
    (hpair : ∀ j k : Fin K, j ≠ k → I j ⊔ I k = ⊤) :
    (⨅ j : Fin K, I j ^ n) = (⨅ j : Fin K, I j) ^ n := by
  classical
  have hprod_pow : (∏ j : Fin K, I j ^ n) = ⨅ j : Fin K, I j ^ n := by
    simpa using
      (Ideal.prod_eq_iInf_of_pairwise_isCoprime
        (s := Finset.univ) (J := fun j : Fin K => I j ^ n)
        (by
          intro j hj k hk hne
          exact (Ideal.isCoprime_iff_sup_eq).2
            (Ideal.pow_sup_pow_eq_top (hpair j k hne))))
  have hprod : (∏ j : Fin K, I j) = ⨅ j : Fin K, I j := by
    simpa using
      (Ideal.prod_eq_iInf_of_pairwise_isCoprime
        (s := Finset.univ) (J := I)
        (by
          intro j hj k hk hne
          exact (Ideal.isCoprime_iff_sup_eq).2 (hpair j k hne)))
  calc
    (⨅ j : Fin K, I j ^ n) = ∏ j : Fin K, I j ^ n := hprod_pow.symm
    _ = (∏ j : Fin K, I j) ^ n := Finset.prod_pow _ _ _
    _ = (⨅ j : Fin K, I j) ^ n := congrArg (fun J : Ideal R => J ^ n) hprod