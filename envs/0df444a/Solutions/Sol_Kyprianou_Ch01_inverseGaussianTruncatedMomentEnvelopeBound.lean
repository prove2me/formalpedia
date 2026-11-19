-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianTruncatedMomentEnvelopeBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T01:01:19.858566+00:00
-- url     : https://prove2.me/submissions/a7802742-9bb4-4c93-a58b-c89c722f7642

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianTruncatedMomentEnvelopeNearZero
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianTruncatedMomentEnvelopeTail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (b x : ℝ) (hb : 0 < b) (hx : 0 < x) :
    (min 1 (x ^ 2)) *
      ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2))) ≤
      (if x ≤ 1 then x ^ (-(1 / 2 : ℝ))
        else x ^ (-(3 / 2 : ℝ))) := by
  by_cases hsmall : x ≤ 1
  · simpa only [if_pos hsmall] using
      Kyprianou.Ch01.inverseGaussianTruncatedMomentEnvelopeNearZero
        b x hb hx hsmall
  · have hlarge : 1 < x := lt_of_not_ge hsmall
    simpa only [if_neg hsmall] using
      Kyprianou.Ch01.inverseGaussianTruncatedMomentEnvelopeTail
        b x hb hx hlarge
