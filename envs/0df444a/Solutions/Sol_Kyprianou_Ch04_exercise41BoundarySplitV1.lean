-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41BoundarySplitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:43:21.816752+00:00
-- url     : https://prove2.me/submissions/89663aee-3d4b-4ff9-bb5c-1cd28ae0da32

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_smallTimeDriftLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04

/-- Subtract the one-sided values to form a continuous part and represent the remaining difference by two indicators for the weak and strict positive half-lines. -/
theorem solution
    (f fLeft fRight : ℝ → ℝ)
    (hLeft : ∀ x : ℝ, x < 0 → f x = fLeft x)
    (hRight : ∀ x : ℝ, 0 < x → f x = fRight x)
    (x : ℝ) :
    f x =
      (if x < 0 then fLeft x - fLeft 0
        else if 0 < x then fRight x - fRight 0 else 0) +
      fLeft 0 + (if 0 ≤ x then f 0 - fLeft 0 else 0) +
      (if 0 < x then fRight 0 - f 0 else 0) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [hLeft x hx]
    simp [hx, not_le_of_gt hx, not_lt_of_ge hx.le]
  · simp
  · rw [hRight x hx]
    simp [hx, not_lt_of_ge hx.le, hx.le]
