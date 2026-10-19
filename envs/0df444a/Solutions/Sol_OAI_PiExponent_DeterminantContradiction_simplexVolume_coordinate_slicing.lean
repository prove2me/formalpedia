-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_coordinate_slicing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:56:05.487617+00:00
-- url     : https://prove2.me/submissions/ee61330f-5a6d-4a32-87e1-44cd82bc3b19

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_coordinate_slicing_general

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ (1 : ℝ)}) =
    ∫ t in (0 : ℝ)..1, ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1 - t}) := by
  simpa using
    OAI.PiExponent.DeterminantContradiction.simplexVolume_coordinate_slicing_general
      n (1 : ℝ) (by norm_num)