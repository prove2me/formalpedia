-- Prove2me | solution 1 for Kyprianou.Ch04.compactDifferenceSquareRangeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:26:50.161813+00:00
-- url     : https://prove2.me/submissions/3e1e3309-c4ff-415e-9d3b-4852deef30be

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

/-- Compact absolute bounds imply boundedness of the squared difference range. -/
theorem solution (U V : NNReal → ℝ) (T : NNReal)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : ∀ t ≤ T, |U t| ≤ A)
    (hv : ∀ t ≤ T, |V t| ≤ B) :
    BddAbove ((fun t : NNReal => |U t - V t|^2) '' Iic T) := by
  refine ⟨(A+B)^2, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  have h : |U t - V t| ≤ A+B :=
    (abs_sub _ _).trans (add_le_add (hu t ht) (hv t ht))
  change |U t - V t|^2 ≤ (A+B)^2
  exact pow_le_pow_left₀ (abs_nonneg _) h 2
