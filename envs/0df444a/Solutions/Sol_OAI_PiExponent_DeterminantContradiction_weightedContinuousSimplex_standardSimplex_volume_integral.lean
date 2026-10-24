-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:35:40.88437+00:00
-- url     : https://prove2.me/submissions/a49453fa-ad4e-49e7-b544-d23c91c85cb5

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_integrand_nonnegative_integrable
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_ofReal_integral_bridge
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_real_power_integral

open scoped BigOperators

theorem solution (n : Nat) (T : Real) (hT : 0 < T) :
    (∫⁻ t in Set.Ioo (0 : Real) T,
      ENNReal.ofReal ((T - t) ^ n / (n.factorial : Real)) ∂MeasureTheory.volume) =
      ENNReal.ofReal (T ^ (n + 1) / ((n + 1).factorial : Real)) := by
  have hprops :=
    OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_integrand_nonnegative_integrable
      n T hT
  rw [OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_ofReal_integral_bridge
    (Set.Ioo (0 : Real) T)
    (fun t => (T - t) ^ n / (n.factorial : Real)) hprops.1 hprops.2]
  exact congrArg ENNReal.ofReal
    (OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_real_power_integral
      n T hT)