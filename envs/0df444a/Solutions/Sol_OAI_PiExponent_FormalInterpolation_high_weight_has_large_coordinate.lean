-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.high_weight_has_large_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:44:21.778752+00:00
-- url     : https://prove2.me/submissions/1a4af27d-a932-4dc0-a24a-339294143da0

import Mathlib
open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (n : Fin d → Nat) (hn : ∀ i, 0 < n i)
    (e : Fin d →₀ Nat)
    (hweight : (∑ i : Fin d, ((n i : ℚ) - 1) * w i) < Finsupp.weight w e) :
    ∃ i : Fin d, n i ≤ e i := by
  by_contra h
  push Not at h
  apply absurd hweight
  rw [not_lt, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  apply Finset.sum_le_sum
  intro i _
  have hwi : (0:ℚ) < w i := by exact_mod_cast hw i
  have : (e i : ℚ) ≤ (n i : ℚ) - 1 := by
    have := h i
    have : e i + 1 ≤ n i := this
    have : ((e i + 1 : ℕ) : ℚ) ≤ n i := by exact_mod_cast this
    push_cast at this; linarith
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right this hwi.le
