-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneTripletIntegralSplitNonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:03:00.919194+00:00
-- url     : https://prove2.me/submissions/86db67ae-6e0b-4608-bbc7-5a505f430da9

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (cpos cneg : ℝ) (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg) :
    let alpha : ℝ := 1
    let muPos : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1)))
    let muNeg : Measure ℝ := (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)))
    T.gaussianVariance = 0 →
    T.levyMeasure = muPos + muNeg →
    ∀ xi : ℝ, -Kyprianou.Ch01.levyTripleExponent T xi =
      -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) -
      (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muPos) -
      (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muNeg)
      := by
  intro alpha muPos muNeg hVar hPi xi
  have hLevy : ProbabilityTheory.IsLevyMeasure T.levyMeasure := by
    first
    | exact T.isLevyMeasure
    | exact T.levyMeasure_isLevy
    | exact T.levyMeasure_isLevyMeasure
    | exact T.isLevy
  have hIntegrable :
      Integrable (ProbabilityTheory.levyCompensatedIntegrand xi)
        (muPos + muNeg) := by
    rw [← hPi]
    exact ProbabilityTheory.integrable_levyCompensatedIntegrand hLevy xi
  have hp : Integrable (ProbabilityTheory.levyCompensatedIntegrand xi) muPos :=
    hIntegrable.left_of_add_measure
  have hn : Integrable (ProbabilityTheory.levyCompensatedIntegrand xi) muNeg :=
    hIntegrable.right_of_add_measure
  unfold Kyprianou.Ch01.levyTripleExponent
  rw [hVar, hPi, integral_add_measure hp hn]
  push_cast
  ring
