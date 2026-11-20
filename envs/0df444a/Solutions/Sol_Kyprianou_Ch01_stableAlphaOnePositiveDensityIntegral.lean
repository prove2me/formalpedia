-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOnePositiveDensityIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:38:56.816882+00:00
-- url     : https://prove2.me/submissions/8c593a92-c493-41d5-b22a-bc82e2d64814

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution (c xi : ℝ) (hc : 0 ≤ c) :
    (∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r ∂
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (c * r ^ (-2 : ℝ))))) =
    (∫ r in Set.Ioi (0 : ℝ),
      (c * r ^ (-2 : ℝ)) •
        ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) := by
  let mu : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (c * r ^ (-2 : ℝ))
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hfin : ∀ᵐ r ∂mu, f r < ∞ := by
    filter_upwards [] with r
    exact ENNReal.ofReal_lt_top
  change (∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r
      ∂mu.withDensity f) = _
  rw [integral_withDensity_eq_integral_toReal_smul hf hfin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hp : 0 ≤ c * r ^ (-2 : ℝ) :=
    mul_nonneg hc (Real.rpow_nonneg hr.le _)
  simp only [f, ENNReal.toReal_ofReal hp]
