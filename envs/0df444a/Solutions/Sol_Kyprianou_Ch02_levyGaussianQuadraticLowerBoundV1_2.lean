-- Prove2me | solution 2 for Kyprianou.Ch02.levyGaussianQuadraticLowerBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:20:30.92217+00:00
-- url     : https://prove2.me/submissions/31dc56c2-e581-479b-b52f-07b2d37d8aff

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
      -(Kyprianou.Ch01.levyTripleExponent T ξ).re  := by
  have hi := ProbabilityTheory.integrable_levyCompensatedIntegrand
    T.levyMeasure_isLevyMeasure ξ
  have hj : ∀ x : ℝ, (ProbabilityTheory.levyCompensatedIntegrand ξ x).re ≤ 0 := by
    intro x
    rw [ProbabilityTheory.levyCompensatedIntegrand_def]
    by_cases hx : |x| < 1
    · simp [hx, Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.sub_re]
      exact Real.cos_le_one _
    · simp [hx, Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.sub_re]
      exact Real.cos_le_one _
  have hJ : (∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂T.levyMeasure).re ≤ 0 := by
    change RCLike.re (∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂T.levyMeasure) ≤ 0
    rw [← integral_re hi]
    exact integral_nonpos hj
  unfold Kyprianou.Ch01.levyTripleExponent
  simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.normSq, pow_two] at *
  linarith
