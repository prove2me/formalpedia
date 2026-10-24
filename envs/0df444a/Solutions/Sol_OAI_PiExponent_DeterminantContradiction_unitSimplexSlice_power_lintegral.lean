-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_power_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:24:01.05529+00:00
-- url     : https://prove2.me/submissions/d42de43f-acf0-4206-a47e-c4f1b6f852f7

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlice_lintegral_to_intervalIntegral
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlice_intervalIntegral_eval

open MeasureTheory

theorem solution (n : Nat) :
    ∫⁻ t : Real,
      (if t ∈ Set.Icc (0 : Real) 1 then
        ENNReal.ofReal ((1 - t) ^ n / (n.factorial : Real))
      else 0) ∂MeasureTheory.volume =
    ENNReal.ofReal (1 / ((n + 1).factorial : Real)) := by
  rw [OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_lintegral_to_intervalIntegral,
    OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_intervalIntegral_eval]