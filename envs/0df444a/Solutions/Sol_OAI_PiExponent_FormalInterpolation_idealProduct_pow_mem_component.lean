-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.idealProduct_pow_mem_component
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:18:03.912991+00:00
-- url     : https://prove2.me/submissions/ee926081-5363-4324-a153-10b05ccc232d

import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators

theorem solution {A : Type} [CommSemiring A] {K : Nat} (I : Fin K → Ideal A)
    (x : A) (n : Nat) (j : Fin K)
    (hx : x ∈ (∏ k : Fin K, I k) ^ n) : x ∈ I j ^ n := by
  have hprod : (∏ k : Fin K, I k) ≤ I j := by
    calc
      (∏ k : Fin K, I k) = (Finset.univ : Finset (Fin K)).prod I := by simp
      _ ≤ (Finset.univ : Finset (Fin K)).inf I := Ideal.prod_le_inf
      _ ≤ I j := Finset.inf_le (Finset.mem_univ j)
  exact (Ideal.pow_right_mono hprod n) hx