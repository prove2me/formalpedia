-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_slice_repair4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:53:58.650604+00:00
-- url     : https://prove2.me/submissions/4a04aad2-29f6-4517-8c01-7698494cc93d

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_slice_recurrence

open MeasureTheory

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
  rw [OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_slice_recurrence, h]
  rw [← ENNReal.ofReal_mul (by positivity)]