-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanBrownianPhiHarmonicRoot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:46:37.406144+00:00
-- url     : https://prove2.me/submissions/e3d3c991-4cdf-4351-bca8-2c8d7cd8745e

import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Positivity

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (sigma gamma q : ℝ) (hsigma : 0 < sigma) (hq : 0 < q) :
    let phi : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
        sigma ^ 2
    (sigma ^ 2 / 2) * phi ^ 2 - gamma * phi - q = 0 := by
  dsimp only
  have hs : sigma ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hsigma)
  have hrad : 0 ≤ gamma ^ 2 + 2 * sigma ^ 2 * q := by positivity
  have hroot : (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q)) ^ 2 =
      gamma ^ 2 + 2 * sigma ^ 2 * q := Real.sq_sqrt hrad
  field_simp [hs]
  have hradEq : gamma ^ 2 + sigma ^ 2 * 2 * q =
      gamma ^ 2 + 2 * sigma ^ 2 * q := by ring
  rw [hradEq]
  nlinarith [hroot]
