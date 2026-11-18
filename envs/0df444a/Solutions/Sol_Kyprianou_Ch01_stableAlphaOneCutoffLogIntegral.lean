-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCutoffLogIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:45:12.364288+00:00
-- url     : https://prove2.me/submissions/d12d2fd1-e086-498f-8044-8ce16274f018

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! Positive logarithmic antiderivative of the scale-cutoff 1/r kernel. -/
theorem solution
    (z : ℝ) (hz : 0 < z) :
    (∫ r : ℝ in (1 : ℝ)..z, r⁻¹) = Real.log z := by
  simpa using (integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) hz)
