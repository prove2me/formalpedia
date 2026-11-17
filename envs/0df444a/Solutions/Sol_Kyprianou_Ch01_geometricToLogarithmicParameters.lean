-- Prove2me | solution 1 for Kyprianou.Ch01.geometricToLogarithmicParameters
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:19:17.936798+00:00
-- url     : https://prove2.me/submissions/1c9b81dc-91da-4b44-aa46-a332cb0f621f

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Geometric
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

/-! The compound-Poisson jump parameter and rate are valid in the strict case. -/
theorem solution
    (p : unitInterval.Elem) (hp : p ≠ 0)
    (hp1 : (p : ℝ) < 1) :
    0 < 1 - (p : ℝ) ∧
    1 - (p : ℝ) < 1 ∧
    0 < -Real.log (p : ℝ) := by
  have hpne : (p : ℝ) ≠ 0 := by
    intro h
    apply hp
    exact Subtype.ext h
  have hpnonneg : 0 ≤ (p : ℝ) := p.property.1
  have hppos : 0 < (p : ℝ) := lt_of_le_of_ne hpnonneg (Ne.symm hpne)
  refine ⟨sub_pos.mpr hp1, sub_lt_self 1 hppos, ?_⟩
  exact neg_pos.mpr (Real.log_neg hppos hp1)
