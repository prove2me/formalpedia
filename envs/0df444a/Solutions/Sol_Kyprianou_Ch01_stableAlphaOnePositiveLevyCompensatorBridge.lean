-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOnePositiveLevyCompensatorBridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:40:19.795261+00:00
-- url     : https://prove2.me/submissions/25967ba7-a874-46e5-8814-f31b65c966a7

import Mathlib
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory MeasureTheory Complex Set Real
set_option autoImplicit false
/-! The positive book convention is the negative LeanLevy compensated characteristic-exponent kernel. -/
theorem solution
    (xi r : ℝ) (hr : 0 < r) :
    -(ProbabilityTheory.levyCompensatedIntegrand xi r) /
      ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) =
      ((1 : ℂ) - Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
      Complex.I * (((xi * r : ℝ) : ℂ)) *
        (if r < 1 then (1 : ℂ) else 0)) /
      ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) := by
  have hc : (if |r| < 1 then (1 : ℂ) else 0) =
      if r < 1 then (1 : ℂ) else 0 := by
    rw [abs_of_pos hr]
  have he :
      Complex.exp ((r : ℂ) * (xi : ℂ) * Complex.I) =
      Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) := by
    congr 1
    push_cast
    ring
  unfold ProbabilityTheory.levyCompensatedIntegrand
  rw [he, hc]
  push_cast
  ring
