-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:45:59.74348+00:00
-- url     : https://prove2.me/submissions/d1bd0bcf-e94a-4db2-a2f5-16448b07d4a8

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_power_lintegral_eq_ofReal_integral
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_power_real_integral
open scoped BigOperators
open MeasureTheory

theorem solution (m : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
      if 0 ≤ t ∧ t < T then ENNReal.ofReal (((T - t) / T) ^ m)
      else 0) =
      ENNReal.ofReal (T / ((m + 1 : Nat) : Real)) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral_eq_ofReal_integral m T hT,
    OAI.PiExponent.DeterminantContradiction.simplex_power_real_integral m T hT]
