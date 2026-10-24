-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_lintegral_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:16:18.205631+00:00
-- url     : https://prove2.me/submissions/dbdb0b30-efe6-43a0-b739-58f34e20431f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlice_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlice_power_lintegral

open MeasureTheory

theorem solution (n : Nat) :
    ∫⁻ t : Real,
      (if t ∈ Set.Icc (0 : Real) 1 then
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
            (Finset.univ.sum fun i : Fin n => x i) ≤ 1 - t}
      else 0) ∂ MeasureTheory.volume =
    ENNReal.ofReal (1 / ((n + 1).factorial : Real)) := by
  have hfun :
      (fun t : Real =>
        if t ∈ Set.Icc (0 : Real) 1 then
          MeasureTheory.volume
            {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
              (Finset.univ.sum fun i : Fin n => x i) ≤ 1 - t}
        else 0) =
      (fun t : Real =>
        if t ∈ Set.Icc (0 : Real) 1 then
          ENNReal.ofReal ((1 - t) ^ n / (n.factorial : Real))
        else 0) := by
    funext t
    by_cases ht : t ∈ Set.Icc (0 : Real) 1
    · simp [ht,
        OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_volume
          n t ht]
    · simp [ht]
  rw [hfun]
  exact OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_power_lintegral n
