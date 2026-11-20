-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaPowerTripletIntegralSplit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:51:59.810016+00:00
-- url     : https://prove2.me/submissions/fea812b6-5888-4d28-886c-98554fcac1d9

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Theorems.Thm_Kyprianou_Ch01_stableAlphaPowerTwoSidedIntegralSplit
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (alpha cpos cneg xi : ℝ) (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg) :
    let muPos : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (cpos * r ^ (-alpha - 1)))
    let muNeg : Measure ℝ :=
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (cneg * |r| ^ (-alpha - 1)))
    T.levyMeasure = muPos + muNeg →
    (∫ r, ProbabilityTheory.levyCompensatedIntegrand xi r ∂T.levyMeasure) =
      (∫ r in Set.Ioi (0 : ℝ),
        (cpos * r ^ (-alpha - 1)) •
          ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) +
      (∫ r in Set.Iio (0 : ℝ),
        (cneg * |r| ^ (-alpha - 1)) •
          ProbabilityTheory.levyCompensatedIntegrand xi r ∂volume) := by
  intro muPos muNeg hmeasure
  have htot :
      Integrable (ProbabilityTheory.levyCompensatedIntegrand xi)
        (muPos + muNeg) := by
    rw [← hmeasure]
    exact ProbabilityTheory.integrable_levyCompensatedIntegrand
      T.levyMeasure_isLevyMeasure xi
  have hpos : Integrable
      (ProbabilityTheory.levyCompensatedIntegrand xi) muPos :=
    htot.mono_measure (Measure.le_add_right le_rfl)
  have hneg : Integrable
      (ProbabilityTheory.levyCompensatedIntegrand xi) muNeg :=
    htot.mono_measure (Measure.le_add_left le_rfl)
  rw [hmeasure]
  exact Kyprianou.Ch01.stableAlphaPowerTwoSidedIntegralSplit
    alpha cpos cneg xi hcpos hcneg hpos hneg
