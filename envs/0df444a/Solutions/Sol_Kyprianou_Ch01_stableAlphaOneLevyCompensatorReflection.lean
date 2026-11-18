-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLevyCompensatorReflection
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:53:30.390167+00:00
-- url     : https://prove2.me/submissions/fe599283-c944-4c13-adcf-f089594fef66

import Mathlib
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory MeasureTheory Complex Set Real
set_option autoImplicit false
/-! Reflection of jump signs reverses frequency inside the compensated Lévy exponent. -/
theorem solution
    (xi r : ℝ) :
    ProbabilityTheory.levyCompensatedIntegrand xi (-r) =
      ProbabilityTheory.levyCompensatedIntegrand (-xi) r := by
  have hExp :
      Complex.exp (((-r : ℝ) : ℂ) * (xi : ℂ) * Complex.I) =
      Complex.exp ((r : ℂ) * (((-xi : ℝ) : ℂ)) * Complex.I) := by
    congr 1
    push_cast
    ring
  unfold ProbabilityTheory.levyCompensatedIntegrand
  simp only [abs_neg, hExp]
  push_cast
  ring
