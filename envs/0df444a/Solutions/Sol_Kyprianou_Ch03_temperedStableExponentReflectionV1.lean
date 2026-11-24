-- Prove2me | solution 1 for Kyprianou.Ch03.temperedStableExponentReflectionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:43:05.944225+00:00
-- url     : https://prove2.me/submissions/e3565c46-f4a6-4ea2-9a09-e8ed6648a3b8

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_ProbabilityTheory_measurable_levyCompensatedIntegrand
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu : Measure ℝ) (xi : ℝ) :
    (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂(mu.map (fun x : ℝ => -x))) =
    ∫ x, ProbabilityTheory.levyCompensatedIntegrand (-xi) x ∂mu := by
  have hf := ProbabilityTheory.measurable_levyCompensatedIntegrand xi
  rw [integral_map measurable_neg.aemeasurable hf.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Function.comp_apply, ProbabilityTheory.levyCompensatedIntegrand,
    abs_neg, Complex.ofReal_neg, neg_mul, mul_neg]
