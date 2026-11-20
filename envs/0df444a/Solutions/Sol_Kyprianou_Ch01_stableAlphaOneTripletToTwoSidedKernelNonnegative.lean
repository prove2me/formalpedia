-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneTripletToTwoSidedKernelNonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:21:03.544671+00:00
-- url     : https://prove2.me/submissions/0a881a37-06da-45af-8dc0-01b81d9bd4f9

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneTripletIntegralSplitNonnegative
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOnePositiveTripletKernelIntegral
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneNegativeTripletKernelIntegral
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
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) +
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)))
    let F : ℝ → ℂ := fun xi =>
      ∫ r in Set.Ioi (0 : ℝ),
        ((1 : ℂ) - Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
            Complex.I * (((xi * r : ℝ) : ℂ)) *
              (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume
    T.gaussianVariance = 0 →
    T.levyMeasure = Pi →
    ∀ xi : ℝ,
      -Kyprianou.Ch01.levyTripleExponent T xi =
      -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) +
        (cpos : ℂ) * F xi + (cneg : ℂ) * F (-xi) := by
  intro alpha Pi F hVar hPi xi
  let muPos : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1)))
  let muNeg : Measure ℝ := (volume.restrict (Set.Iio (0 : ℝ))).withDensity
      (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)))
  have hMeasure : T.levyMeasure = muPos + muNeg := by
    simpa only [Pi, muPos, muNeg] using hPi
  have hSplit :
      -Kyprianou.Ch01.levyTripleExponent T xi =
        -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) - (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muPos) - (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muNeg) := by
    simpa only [muPos, muNeg] using
      (Kyprianou.Ch01.stableAlphaOneTripletIntegralSplitNonnegative
        T cpos cneg hcpos hcneg hVar hMeasure xi)
  have hPositive : -(∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muPos) = (cpos : ℂ) * F xi := by
    simpa only [muPos, F] using
      (Kyprianou.Ch01.stableAlphaOnePositiveTripletKernelIntegral
        cpos xi hcpos)
  have hNegative : -(∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muNeg) = (cneg : ℂ) * F (-xi) := by
    simpa only [muNeg, F] using
      (Kyprianou.Ch01.stableAlphaOneNegativeTripletKernelIntegral
        cneg xi hcneg)
  calc
    -Kyprianou.Ch01.levyTripleExponent T xi =
      -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) - (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muPos) - (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muNeg) := hSplit
    _ = -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) + (cpos : ℂ) * F xi +
          (cneg : ℂ) * F (-xi) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, hPositive, hNegative]
