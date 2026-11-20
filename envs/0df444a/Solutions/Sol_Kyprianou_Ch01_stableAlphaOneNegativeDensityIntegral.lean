-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneNegativeDensityIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:23:59.532341+00:00
-- url     : https://prove2.me/submissions/210e15a7-f7b5-4081-b228-e87b0a8b8314

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOnePositiveWeightedJumpKernel
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLevyCompensatorReflection
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (c xi : ℝ) (hc : 0 ≤ c) :
    (∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r ∂
      ((volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (c * |r| ^ (-2 : ℝ))))) =
    (∫ r in Set.Iio (0 : ℝ),
      (c * |r| ^ (-2 : ℝ)) •
        ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) := by
  let mu : Measure ℝ := volume.restrict (Set.Iio (0 : ℝ))
  let f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (c * |r| ^ (-2 : ℝ))
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hfin : ∀ᵐ r ∂mu, f r < ∞ := by
    filter_upwards [] with r
    exact ENNReal.ofReal_lt_top
  change (∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r
      ∂mu.withDensity f) = _
  rw [integral_withDensity_eq_integral_toReal_smul hf hfin]
  apply setIntegral_congr_fun measurableSet_Iio
  intro r hr
  have hp : 0 ≤ c * |r| ^ (-2 : ℝ) :=
    mul_nonneg hc (Real.rpow_nonneg (abs_nonneg _) _)
  simp only [f, ENNReal.toReal_ofReal hp]
