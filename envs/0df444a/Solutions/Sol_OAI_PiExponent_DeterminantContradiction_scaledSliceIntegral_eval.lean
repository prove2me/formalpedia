-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_eval
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:25:05.675721+00:00
-- url     : https://prove2.me/submissions/9fd537c0-61a3-4e2b-8484-ba0b915686dc

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaledSliceIntegral_intervalBridge
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitPower_intervalIntegral

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ∫⁻ t : ℝ,
      (if 0 ≤ t ∧ t ≤ 1 then ENNReal.ofReal (1 - t) ^ n else 0)
      ∂MeasureTheory.volume = ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
  rw [OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_intervalBridge,
    OAI.PiExponent.DeterminantContradiction.unitPower_intervalIntegral]