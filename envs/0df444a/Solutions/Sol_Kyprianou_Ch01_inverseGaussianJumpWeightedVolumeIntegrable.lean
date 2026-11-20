-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianJumpWeightedVolumeIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:11:16.269855+00:00
-- url     : https://prove2.me/submissions/931bd44b-d7a1-4a7d-b8d1-f62507590359

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpPowerEnvelopeIntegrable
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpWeightedNormEnvelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 < b) :
    ∀ theta : ℝ,
      Integrable
        (fun x : ℝ =>
          (ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2)))).toReal •
            ((1 : ℂ) - Complex.exp
              (Complex.I * ((theta * x : ℝ) : ℂ))))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
  intro theta
  have hmajor :=
    Kyprianou.Ch01.inverseGaussianJumpPowerEnvelopeIntegrable theta
  apply Integrable.mono' hmajor
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Kyprianou.Ch01.inverseGaussianJumpWeightedNormEnvelope
      b theta x hb hx
