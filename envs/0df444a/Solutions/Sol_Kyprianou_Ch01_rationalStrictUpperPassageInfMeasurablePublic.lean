-- Prove2me | solution 1 for Kyprianou.Ch01.rationalStrictUpperPassageInfMeasurablePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:26:39.503754+00:00
-- url     : https://prove2.me/submissions/ceca3134-f5a3-4faf-bba0-ebc1bba993a5

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.NNReal.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
set_option autoImplicit false

/-- The infimum of countably many measurable rational upper-crossing times is measurable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Measurable (fun ω : Ω =>
      ⨅ r : ℚ,
        if (0 < (r : ℝ) ∧ s < X (Real.toNNReal (r : ℝ)) ω)
          then ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0)
          else ⊤) := by
  classical
  apply Measurable.iInf
  intro r
  have hp : MeasurableSet
      {ω : Ω | 0 < (r : ℝ) ∧ s < X (Real.toNNReal (r : ℝ)) ω} := by
    by_cases hr : 0 < (r : ℝ)
    · simp only [hr, true_and]
      exact measurableSet_Ioi.preimage (hMeas _)
    · simp only [hr, false_and]
      exact MeasurableSet.empty
  exact Measurable.ite hp measurable_const measurable_const
