-- Prove2me | solution 1 for Kyprianou.Ch01.withTopPassageZeroOfDiscountOneV1
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T02:42:23.478654+00:00
-- url     : https://prove2.me/submissions/64f1058c-0306-44df-801d-c2f52432f9f4

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
    (T : WithTop ℝ≥0)
    (hOne : (match T with
      | none => (0 : ℝ)
      | some t => Real.exp (-(t : ℝ))) = 1) :
    T ≤ (0 : WithTop ℝ≥0) := by
  cases T with
  | top => norm_num at hOne
  | coe t =>
    change Real.exp (-(t : ℝ)) = 1 at hOne
    have hz : -(t : ℝ) = 0 := Real.exp_injective (by simpa using hOne)
    have ht : t = 0 := by exact_mod_cast (neg_eq_zero.mp hz)
    subst t
    exact le_rfl
