-- Prove2me | solution 1 for Kyprianou.Ch01.charFun_sumWithGaussianMarginal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:05:47.447486+00:00
-- url     : https://prove2.me/submissions/18565756-f70a-4ab4-be41-4ce3c5f4655f

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal
set_option autoImplicit false

theorem solution
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (v : ℝ≥0) (xi : ℝ) :
    charFun ((mu.prod (gaussianReal 0 v)).map
        (fun p : ℝ × ℝ => p.1 + p.2)) xi =
      charFun mu xi *
        Complex.exp (-((v : ℂ) * (xi : ℂ) ^ 2 / 2)) := by
  rw [ProbabilityTheory.charFun_map_add_prod_eq_mul]
  simp only [Pi.mul_apply]
  rw [ProbabilityTheory.charFun_gaussianReal]
  simp <;> ring
