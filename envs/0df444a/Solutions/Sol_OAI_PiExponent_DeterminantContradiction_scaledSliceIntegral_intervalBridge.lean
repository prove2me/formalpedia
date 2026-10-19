-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_intervalBridge
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:38:52.150044+00:00
-- url     : https://prove2.me/submissions/4fb49ee6-1e87-41ea-8640-6858d81f2190

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaledSliceIntegral_lintegral_eval
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaledSliceIntegral_interval_eval

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ∫⁻ t : ℝ,
      (if 0 ≤ t ∧ t ≤ 1 then ENNReal.ofReal (1 - t) ^ n else 0)
      ∂MeasureTheory.volume =
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, (1 - t) ^ n) := by
  rw [OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_lintegral_eval n,
    OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_interval_eval n]