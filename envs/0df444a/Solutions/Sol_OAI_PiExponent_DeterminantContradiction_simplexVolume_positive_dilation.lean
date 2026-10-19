-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_positive_dilation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T08:01:52.556892+00:00
-- url     : https://prove2.me/submissions/723e537b-4a27-4b86-be35-2f93fc03aed6

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_dilation_eq_image
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_realVolume_image_smul
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unit_simplex_measurable

open scoped BigOperators Topology

theorem solution
    (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ r}) =
    r ^ n * ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_dilation_eq_image n r hr]
  exact OAI.PiExponent.DeterminantContradiction.realVolume_image_smul n r hr _
    (OAI.PiExponent.DeterminantContradiction.unit_simplex_measurable n)