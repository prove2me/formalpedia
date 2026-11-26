-- Prove2me | solution 1 for Kyprianou.Ch04.clippedClockCoe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:26:41.154722+00:00
-- url     : https://prove2.me/submissions/6f076bf6-2f0a-4002-853e-c607c0503121

import Mathlib
open scoped NNReal
set_option autoImplicit false

/-- The finite deterministic clipping of an extended clock has the stated coercion. -/
theorem solution (tau : WithTop NNReal) (t : NNReal) :
    (((min tau (t : WithTop NNReal)).untopD t : NNReal) : WithTop NNReal) =
      min tau (t : WithTop NNReal) := by
  induction tau using WithTop.recTopCoe with
  | top => rw [min_eq_right le_top,WithTop.untopD_coe]
  | coe a =>
    by_cases h : a ≤ t
    · rw [min_eq_left (WithTop.coe_le_coe.mpr h),WithTop.untopD_coe]
    · have h' : t ≤ a := (lt_of_not_ge h).le
      rw [min_eq_right (WithTop.coe_le_coe.mpr h'),WithTop.untopD_coe]
