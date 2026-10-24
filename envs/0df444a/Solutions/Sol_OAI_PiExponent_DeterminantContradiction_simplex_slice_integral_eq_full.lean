-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_slice_integral_eq_full
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:02:12.936359+00:00
-- url     : https://prove2.me/submissions/11b5b892-43d7-4d34-82b0-67c3c5f83843

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_integral_eq_indicator
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_full_fiber_eq_indicator_ae

open scoped BigOperators

theorem solution (n : Nat) (T : Real) (hT : 0 < T) :
    (∫⁻ t in Set.Ioo (0 : Real) T,
      MeasureTheory.volume {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t}
        ∂MeasureTheory.volume) =
      (∫⁻ t : Real,
        MeasureTheory.volume {y : Fin n → Real | 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t}
        ∂MeasureTheory.volume) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_slice_integral_eq_indicator n T hT]
  exact MeasureTheory.lintegral_congr_ae
    (OAI.PiExponent.DeterminantContradiction.simplex_full_fiber_eq_indicator_ae n T hT)