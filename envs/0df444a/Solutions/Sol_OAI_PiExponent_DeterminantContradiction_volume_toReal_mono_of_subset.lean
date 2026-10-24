-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.volume_toReal_mono_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:00:05.296351+00:00
-- url     : https://prove2.me/submissions/54a566e4-da19-4fba-ad8d-dd7109c2916b

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem solution
    {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {s t : Set α} (hsub : s ⊆ t) (ht : μ t ≠ ⊤) :
    ENNReal.toReal (μ s) ≤ ENNReal.toReal (μ t) := by
  exact ENNReal.toReal_mono ht (MeasureTheory.measure_mono hsub)