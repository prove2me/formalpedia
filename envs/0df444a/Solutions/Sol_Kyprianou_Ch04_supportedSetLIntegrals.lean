-- Prove2me | solution 1 for Kyprianou.Ch04.supportedSetLIntegrals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:41:20.040376+00:00
-- url     : https://prove2.me/submissions/117ac883-09dc-4969-a653-d010cd2bcff1

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

/-- Nonnegative integral equality on nested sets for a supported kernel. -/
theorem solution {E : Type} [MeasurableSpace E] (mu : Measure E)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V)
    (f : E → ENNReal) (hz : ∀ z ∈ V, z ∉ U → f z = 0) :
    (∫⁻ z in V, f z ∂mu) = ∫⁻ z in U, f z ∂mu := by
  classical
  rw [← lintegral_indicator hV, ← lintegral_indicator hU]
  apply lintegral_congr
  intro z
  by_cases h : z ∈ U
  · simp [Set.indicator_of_mem h, Set.indicator_of_mem (hUV h)]
  · by_cases hv : z ∈ V
    · simp [Set.indicator_of_mem hv, Set.indicator_of_notMem h, hz z hv h]
    · simp [Set.indicator_of_notMem hv, Set.indicator_of_notMem h]
