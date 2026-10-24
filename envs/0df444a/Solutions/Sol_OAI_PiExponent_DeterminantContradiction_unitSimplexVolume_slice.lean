-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_slice
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:32:03.505559+00:00
-- url     : https://prove2.me/submissions/31a9554a-b22b-4737-a286-964c98bc18e5

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_slice_repair4

theorem solution (n : Nat)
    (h : MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real))) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin (n + 1) => x i) ≤ 1} =
      ENNReal.ofReal
        ((1 / (Nat.factorial n : Real)) *
          (∫ t in (0 : Real)..1, (1 - t) ^ n)) := by
  apply OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_slice_repair4 <;> assumption
