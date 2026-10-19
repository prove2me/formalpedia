-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.ideal_finset_prod_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:43:21.251048+00:00
-- url     : https://prove2.me/submissions/99c1a570-2889-447b-ac35-56bfccd2704d

import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators

theorem solution
    {α R : Type} [Fintype α] [CommSemiring R]
    (A B : α → Ideal R) (r s : Nat)
    (h : ∀ a, A a ^ r ≤ B a ^ s) :
    (∏ a, A a) ^ r ≤ (∏ a, B a) ^ s := by
  rw [← Finset.prod_pow, ← Finset.prod_pow]
  exact Finset.prod_le_prod' (fun a _ => h a)