-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaPowerTwoSidedIntegralSplit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:41:54.455987+00:00
-- url     : https://prove2.me/submissions/67044a24-8cda-4dec-aa0c-3e650adb9917

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaPowerPositiveDensityIntegral
import Theorems.Thm_Kyprianou_Ch01_stableAlphaPowerNegativeDensityIntegral
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (alpha cpos cneg xi : ℝ) (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg) :
    let muPos : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (cpos * r ^ (-alpha - 1)))
    let muNeg : Measure ℝ :=
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (cneg * |r| ^ (-alpha - 1)))
    Integrable (ProbabilityTheory.levyCompensatedIntegrand xi) muPos →
    Integrable (ProbabilityTheory.levyCompensatedIntegrand xi) muNeg →
    (∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r ∂(muPos + muNeg)) =
      (∫ r in Set.Ioi (0 : ℝ),
        (cpos * r ^ (-alpha - 1)) •
          ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) +
      (∫ r in Set.Iio (0 : ℝ),
        (cneg * |r| ^ (-alpha - 1)) •
          ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) := by
  intro muPos muNeg hpos hneg
  rw [integral_add_measure hpos hneg]
  rw [Kyprianou.Ch01.stableAlphaPowerPositiveDensityIntegral
        alpha cpos xi hcpos]
  rw [Kyprianou.Ch01.stableAlphaPowerNegativeDensityIntegral
        alpha cneg xi hcneg]
