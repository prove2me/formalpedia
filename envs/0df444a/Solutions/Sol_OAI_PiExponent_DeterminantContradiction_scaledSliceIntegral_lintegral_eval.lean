-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_lintegral_eval
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:45:26.035014+00:00
-- url     : https://prove2.me/submissions/3867fce1-3119-4f26-ae40-843a82cb0b73

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaledSliceIntegral_lintegral_toRealIntegral
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaledSliceIntegral_real_integral_eval

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ∫⁻ t : ℝ,
      (if 0 ≤ t ∧ t ≤ 1 then ENNReal.ofReal (1 - t) ^ n else 0)
      ∂MeasureTheory.volume =
      ENNReal.ofReal (((n : ℝ) + 1)⁻¹) := by
  rw [OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_lintegral_toRealIntegral,
    OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_real_integral_eval]