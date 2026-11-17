-- Prove2me | solution 2 for Kyprianou.Ch01.charFun_sumWithGaussianMarginal
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:06:00.036955+00:00
-- url     : https://prove2.me/submissions/55fdf85f-aa5e-42b0-b25e-3048605110e5

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.charFun_sumWithGaussianMarginal
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (v : ℝ≥0) (xi : ℝ) :
    charFun ((mu.prod (gaussianReal 0 v)).map
        (fun p : ℝ × ℝ => p.1 + p.2)) xi =
      charFun mu xi *
        Complex.exp (-((v : ℂ) * (xi : ℂ) ^ 2 / 2)) := by
  have h : (mu.prod (gaussianReal 0 v)).map (fun p : ℝ × ℝ => p.1 + p.2) =
      mu ∗ gaussianReal 0 v := rfl
  rw [h, charFun_conv, charFun_gaussianReal]
  congr 1
  congr 1
  push_cast
  ring

theorem solution
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (v : ℝ≥0) (xi : ℝ) :
    charFun ((mu.prod (gaussianReal 0 v)).map
        (fun p : ℝ × ℝ => p.1 + p.2)) xi =
      charFun mu xi *
        Complex.exp (-((v : ℂ) * (xi : ℂ) ^ 2 / 2)) := by
  first
  | exact Kyprianou.Ch01.charFun_sumWithGaussianMarginal
  | exact Kyprianou.Ch01.charFun_sumWithGaussianMarginal ..
  | (intros; apply Kyprianou.Ch01.charFun_sumWithGaussianMarginal <;> assumption)
