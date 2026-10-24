-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux_step
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:47:34.075802+00:00
-- url     : https://prove2.me/submissions/04f5c813-50b1-444d-b6a4-17d7973cbbb6

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_slice_repair4
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplex_slice_integral_repair4
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplex_factorial_step_repair4

theorem solution (n : Nat)
    (h : MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real))) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin (n + 1) => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by
  rw [OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_slice_repair4 n h,
    OAI.PiExponent.DeterminantContradiction.unitSimplex_slice_integral_repair4 n,
    OAI.PiExponent.DeterminantContradiction.unitSimplex_factorial_step_repair4 n]