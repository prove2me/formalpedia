-- Prove2me | solution 1 for Kyprianou.Ch01.geometricRandomSumCharExponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:20:29.704888+00:00
-- url     : https://prove2.me/submissions/2dbe93cb-d848-4c4d-8859-ecf74cd204de

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_geometricMarkCompoundPoissonExponent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

/-! Strict compound-geometric exponent evaluated at an arbitrary real jump law. -/
theorem solution
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (xi : ℝ) :
    Complex.exp (∑' n : ℕ,
      ((((1 - p : ℝ) : ℂ) ^ (n + 1)) / ((n : ℂ) + 1)) *
        ((charFun jumpLaw xi) ^ (n + 1) - 1)) =
      (p : ℂ) / (1 - (((1 - p : ℝ) : ℂ)) * charFun jumpLaw xi) := by
  have hq0 : 0 < 1 - p := sub_pos.mpr hp1
  have hq1 : 1 - p < 1 := sub_lt_self 1 hp0
  have hz : ‖charFun jumpLaw xi‖ ≤ 1 :=
    MeasureTheory.norm_charFun_le_one xi
  have h := Kyprianou.Ch01.geometricMarkCompoundPoissonExponent
    (1 - p) hq0 hq1 (charFun jumpLaw xi) hz
  have hcast : ((1 - (1 - p : ℝ) : ℝ) : ℂ) = (p : ℂ) := by
    congr 1
    ring
  rw [hcast] at h
  exact h
