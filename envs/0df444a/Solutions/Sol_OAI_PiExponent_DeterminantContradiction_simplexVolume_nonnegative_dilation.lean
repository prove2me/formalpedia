-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_nonnegative_dilation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:57:50.052986+00:00
-- url     : https://prove2.me/submissions/ea723567-361b-470c-9683-4ee7a9a73bac

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_positive_dilation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_zero_radius

open scoped BigOperators Topology

theorem solution
    (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ r}) =
    r ^ n * ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) := by
  by_cases hr0 : r = 0
  · subst r
    exact OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_radius n
  · exact OAI.PiExponent.DeterminantContradiction.simplexVolume_positive_dilation
      n r (lt_of_le_of_ne hr (Ne.symm hr0))