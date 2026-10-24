-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:25:41.298986+00:00
-- url     : https://prove2.me/submissions/ed1e7f51-8cb5-4b0d-8b7e-d7865c798daf

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_power_lintegral_scale
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_power_lintegral_scalar
open scoped BigOperators
open MeasureTheory

theorem solution (m : Nat) (T : Real) (hT : 0 < T) (V : ENNReal) :
    MeasureTheory.lintegral MeasureTheory.volume (fun t : Real =>
      if 0 ≤ t ∧ t < T then
        ENNReal.ofReal (((T - t) / T) ^ m) * V
      else 0) =
      ENNReal.ofReal (T / ((m + 1 : Nat) : Real)) * V := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral_scale m T V,
    OAI.PiExponent.DeterminantContradiction.simplex_power_lintegral_scalar m T hT]