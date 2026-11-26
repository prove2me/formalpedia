-- Prove2me | solution 1 for Kyprianou.Ch04.supportedSetIntegrals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:41:19.647202+00:00
-- url     : https://prove2.me/submissions/c16e2634-b149-40b2-a64e-b74b8ce6f3cd

import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

/-- A kernel vanishing outside a smaller set has the same integral on either set. -/
theorem solution {E : Type} [MeasurableSpace E] (mu : Measure E)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V)
    (f : E → ℝ) (hz : ∀ z ∈ V, z ∉ U → f z = 0) :
    (∫ z in V, f z ∂mu) = ∫ z in U, f z ∂mu := by
  classical
  rw [← integral_indicator hV, ← integral_indicator hU]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    by_cases h : z ∈ U
    · simp [Set.indicator_of_mem h, Set.indicator_of_mem (hUV h)]
    · by_cases hv : z ∈ V
      · simp [Set.indicator_of_mem hv, Set.indicator_of_notMem h, hz z hv h]
      · simp [Set.indicator_of_notMem hv, Set.indicator_of_notMem h]
