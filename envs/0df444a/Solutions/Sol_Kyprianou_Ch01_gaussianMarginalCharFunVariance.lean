-- Prove2me | solution 1 for Kyprianou.Ch01.gaussianMarginalCharFunVariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T20:35:47.731585+00:00
-- url     : https://prove2.me/submissions/32c29c49-28e4-43f2-bdb5-509dd303d8ec

import Mathlib.Probability.Distributions.Gaussian.Real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal
set_option autoImplicit false

theorem solution
    (v : ℝ≥0) (ξ : ℝ) :
    charFun (gaussianReal 0 v) ξ =
      Complex.exp (-(((v : ℝ) : ℂ) * (ξ : ℂ) ^ 2 / 2)) := by
  rw [ProbabilityTheory.charFun_gaussianReal]
  simp
