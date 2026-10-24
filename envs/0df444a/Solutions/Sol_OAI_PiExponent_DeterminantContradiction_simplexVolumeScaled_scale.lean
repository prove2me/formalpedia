-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_scale
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:07:23.486419+00:00
-- url     : https://prove2.me/submissions/def9751b-eda1-4f78-817b-f99e348c121c

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_boundary
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_positive
open scoped BigOperators

open MeasureTheory

theorem solution (n : Nat) (r : Real) (hr : 0 ≤ r) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ n) * MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} := by
  by_cases hn : n = 0
  · exact OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_boundary
      n r hr (Or.inl hn)
  by_cases hr0 : r = 0
  · exact OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_boundary
      n r hr (Or.inr hr0)
  have hpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  exact OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_positive
    n r hr hpos