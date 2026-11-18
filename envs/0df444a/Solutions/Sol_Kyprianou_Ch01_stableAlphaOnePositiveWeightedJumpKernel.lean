-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOnePositiveWeightedJumpKernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:48:07.634176+00:00
-- url     : https://prove2.me/submissions/3deed9b8-23c7-4ee4-8143-b41e783a46c0

import Mathlib
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOnePositiveLevyCompensatorBridge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory MeasureTheory Complex Set Real
set_option autoImplicit false
/-! Positive-half-line complex jump integrand after stable density multiplication. -/
theorem solution
    (c xi r : ℝ) (hr : 0 < r) :
    (c * r ^ (-2 : ℝ)) • ProbabilityTheory.levyCompensatedIntegrand xi r =
      -(c : ℂ) * ((1 : ℂ) - Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
        Complex.I * (((xi * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) := by
  have hbridge := Kyprianou.Ch01.stableAlphaOnePositiveLevyCompensatorBridge xi r hr
  have hpow : r ^ (-2 : ℝ) = (r ^ 2)⁻¹ := by
    rw [Real.rpow_neg hr.le]
    exact congrArg (fun a : ℝ => a⁻¹) (Real.rpow_natCast r 2)
  calc
    (c * r ^ (-2 : ℝ)) • ProbabilityTheory.levyCompensatedIntegrand xi r =
        -(c : ℂ) * (-(ProbabilityTheory.levyCompensatedIntegrand xi r) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) := by
          rw [hpow, Complex.real_smul]
          push_cast
          ring
    _ = -(c : ℂ) * ((1 : ℂ) - Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
        Complex.I * (((xi * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) := by
        rw [hbridge]
        ring
