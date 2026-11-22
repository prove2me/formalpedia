-- Prove2me | solution 1 for MasulloRepair.finite_sieve_difference_telescopes
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T21:18:35.192795+00:00
-- url     : https://prove2.me/submissions/b4650689-aee1-448b-a5e8-f3b777a2d1df

import Mathlib

open scoped BigOperators

set_option maxHeartbeats 800000

theorem solution
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (P : ℕ → H →L[ℂ] H) (n : ℕ) :
    (∑ i ∈ Finset.range n, A ∘L (P i - P (i + 1))) =
      A ∘L (P 0 - P n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ext x
      simp [ContinuousLinearMap.comp_apply]
