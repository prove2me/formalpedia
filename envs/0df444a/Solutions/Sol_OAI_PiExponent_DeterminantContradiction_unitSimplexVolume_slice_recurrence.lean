-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_slice_recurrence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:03:46.542957+00:00
-- url     : https://prove2.me/submissions/1a1b8bf7-f266-469b-8582-6d3a0992169c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_eq_lintegral_slices
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlices_lintegral_eval

open MeasureTheory

theorem solution (n : Nat) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin (n + 1) => x i) ≤ 1} =
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
          (Finset.univ.sum fun i : Fin n => x i) ≤ 1} *
        ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) := by
  rw [OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_eq_lintegral_slices,
    OAI.PiExponent.DeterminantContradiction.unitSimplexSlices_lintegral_eval]