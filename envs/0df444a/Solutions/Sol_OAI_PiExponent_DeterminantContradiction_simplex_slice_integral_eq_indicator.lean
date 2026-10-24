-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_slice_integral_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:12:18.655181+00:00
-- url     : https://prove2.me/submissions/cfde8aa2-d75b-442a-a1b2-11ba6264736d

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators

theorem solution (n : Nat) (T : Real) (hT : 0 < T) :
    (∫⁻ t in Set.Ioo (0 : Real) T,
      MeasureTheory.volume {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - t}
        ∂MeasureTheory.volume) =
    (∫⁻ t : Real,
      Set.indicator (Set.Ioo (0 : Real) T)
        (fun u : Real => MeasureTheory.volume
          {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T - u}) t
        ∂MeasureTheory.volume) := by
  exact (MeasureTheory.lintegral_indicator measurableSet_Ioo _).symm