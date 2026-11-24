-- Prove2me | solution 1 for Kyprianou.Ch02.levyGaussianQuadraticLowerBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:18:41.576845+00:00
-- url     : https://prove2.me/submissions/59d55b0f-40da-407c-8cf5-a4d8bf71c35d

import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Theorems.Thm_ProbabilityTheory_levyCompensatedIntegrand_def
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) (ξ : ℝ) :
    (T.gaussianVariance : ℝ) * ξ ^ 2 / 2 ≤
      -(Kyprianou.Ch01.levyTripleExponent T ξ).re := by
  have hi := ProbabilityTheory.integrable_levyCompensatedIntegrand
    T.levyMeasure_isLevyMeasure ξ
  have hr : (∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂T.levyMeasure).re ≤ 0 := by
    change RCLike.re (∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂T.levyMeasure) ≤ 0
    rw [← integral_re hi]
    apply integral_nonpos_of_ae
    filter_upwards [] with x
    change (ProbabilityTheory.levyCompensatedIntegrand ξ x).re ≤ 0
    rw [ProbabilityTheory.levyCompensatedIntegrand_def]
    by_cases hx : |x| < 1
    · simp [hx, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.exp_re]
      exact Real.cos_le_one _
    · simp [hx, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.exp_re]
      exact Real.cos_le_one _
  unfold Kyprianou.Ch01.levyTripleExponent
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  linarith
