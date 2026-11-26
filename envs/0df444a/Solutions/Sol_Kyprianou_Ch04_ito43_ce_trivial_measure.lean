-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ce_trivial_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:10:57.331855+00:00
-- url     : https://prove2.me/submissions/a2dc049b-1281-4b70-ad0f-7c38f1ce3fa5

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

/-- On the trivial sigma algebra, every nonempty set has outer probability one. -/
theorem solution {Ω : Type} (P : @Measure Ω ⊥) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : A.Nonempty) : P A = 1 := by
  letI : MeasurableSpace Ω := ⊥
  have h := MeasurableSpace.measurableSet_bot_iff.mp
    (measurableSet_toMeasurable P A)
  rcases h with h | h
  · exact (hA.ne_empty (subset_empty_iff.mp (h ▸ subset_toMeasurable P A))).elim
  · rw [← measure_toMeasurable A, h, measure_univ]
