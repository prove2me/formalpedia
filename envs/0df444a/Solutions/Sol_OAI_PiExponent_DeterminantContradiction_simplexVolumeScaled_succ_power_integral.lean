-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_power_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:59:19.386985+00:00
-- url     : https://prove2.me/submissions/eb5c3c89-4b21-40df-98d4-81337eed870d

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_succ_power_integral_ennreal_ofReal_integral
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_succ_power_real_integral

open scoped BigOperators

theorem solution
    (n : Nat) (r : Real) (hr : 0 <= r) :
    (∫⁻ t in Set.Icc (0 : Real) r,
        ENNReal.ofReal ((r - t) ^ n / (Nat.factorial n : Real))
        ∂MeasureTheory.volume) =
      ENNReal.ofReal (r ^ (n + 1) / (Nat.factorial (n + 1) : Real)) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_power_integral_ennreal_ofReal_integral n r hr]
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_power_real_integral n r hr]