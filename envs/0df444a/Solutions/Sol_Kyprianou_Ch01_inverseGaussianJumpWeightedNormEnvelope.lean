-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianJumpWeightedNormEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:15:13.285456+00:00
-- url     : https://prove2.me/submissions/6a900bfa-86ef-4043-80bd-737fed9a4fd9

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpWeightedNormEnvelopeNearZero
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpWeightedNormEnvelopeTail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (b theta x : ℝ) (hb : 0 < b) (hx : 0 < x) :
    ‖(ENNReal.ofReal
         ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
           Real.exp (-(b ^ 2 * x / 2)))).toReal •
           ((1 : ℂ) - Complex.exp
             (Complex.I * ((theta * x : ℝ) : ℂ)))‖ ≤ (|theta| + 2) * (if x ≤ 1 then x ^ (-(1 / 2 : ℝ)) else x ^ (-(3 / 2 : ℝ))) := by
  by_cases hsmall : x ≤ 1
  · simpa only [if_pos hsmall] using
      Kyprianou.Ch01.inverseGaussianJumpWeightedNormEnvelopeNearZero
        b theta x hb hx hsmall
  · have hfar : 1 < x := lt_of_not_ge hsmall
    simpa only [if_neg hsmall] using
      Kyprianou.Ch01.inverseGaussianJumpWeightedNormEnvelopeTail
        b theta x hb hfar
