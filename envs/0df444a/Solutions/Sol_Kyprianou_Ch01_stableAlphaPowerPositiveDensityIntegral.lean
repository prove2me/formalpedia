-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaPowerPositiveDensityIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:38:18.714848+00:00
-- url     : https://prove2.me/submissions/b86836a7-353b-423f-a9cc-fef086bedd07

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution (alpha c xi : ℝ) (hc : 0 ≤ c) :
    (∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r ∂
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (c * r ^ (-alpha - 1))))) =
    (∫ r in Set.Ioi (0 : ℝ),
      (c * r ^ (-alpha - 1)) •
        ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) := by
  let mu : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (c * r ^ (-alpha - 1))
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
  have hp : 0 ≤ c * r ^ (-alpha - 1) :=
    mul_nonneg hc (Real.rpow_nonneg hr.le _)
  simp only [f, ENNReal.toReal_ofReal hp]
