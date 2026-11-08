-- Prove2me | solution 1 for LightningNetwork.RateBounds.eq_19_cosh_bound
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T14:57:50.465211+00:00
-- url     : https://prove2.me/submissions/04be5ab0-15ed-4a79-a010-ba1649015095

import Mathlib

/-- Lightning Network economics, inequality (19): `cosh x ≤ (e^{|x|} + 1)/2`. -/
theorem solution :
    (∀ x : ℝ, Real.cosh x ≤ (Real.exp |x| + 1) / 2) ∧
      ∀ C α : ℝ, 2 * (Real.cosh (C - α) - 1) ≤ Real.exp |C - α| - 1 := by
  have hmain : ∀ x : ℝ, Real.cosh x ≤ (Real.exp |x| + 1) / 2 := by
    intro x
    rw [Real.cosh_eq]
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      have h : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    · rw [abs_of_neg (by linarith)]
      have h : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
  exact ⟨hmain, fun C α => by
    have := hmain (C - α)
    linarith⟩
