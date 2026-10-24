-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_eq_lintegral_slices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:08:25.502674+00:00
-- url     : https://prove2.me/submissions/c0f35f6b-73a0-48d1-a2e9-6e8f57a47138

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_cutoff
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlice_lintegral_eq_factorial

open MeasureTheory

theorem solution (n : Nat) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin (n + 1) => x i) ≤ 1} =
      ∫⁻ t : Real,
        (if t ∈ Set.Icc (0 : Real) 1 then
          MeasureTheory.volume
            {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
              (Finset.univ.sum fun i : Fin n => x i) ≤ 1 - t}
        else 0) ∂MeasureTheory.volume := by
  calc
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧
          (Finset.univ.sum fun i : Fin (n + 1) => x i) ≤ 1} =
        ENNReal.ofReal (1 / ((n + 1).factorial : Real)) := by
          simpa using
            OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_cutoff
              (n + 1) (1 : Real)
    _ = ∫⁻ t : Real,
        (if t ∈ Set.Icc (0 : Real) 1 then
          MeasureTheory.volume
            {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
              (Finset.univ.sum fun i : Fin n => x i) ≤ 1 - t}
        else 0) ∂MeasureTheory.volume :=
          (OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_lintegral_eq_factorial n).symm