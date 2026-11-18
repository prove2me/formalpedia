-- Prove2me | solution 1 for Kyprianou.Ch06.firstMarkCompetingRegionIntensitySplit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:43:59.850021+00:00
-- url     : https://prove2.me/submissions/5534e0b3-c875-469c-8ccc-924ed29592f0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {E : Type} [MeasurableSpace E] (n : Measure E)
    (A C : Set E) (hC : MeasurableSet C)
    (hFinite : n A < ⊤) :
    n (A ∩ C) + n (A \ C) = n A ∧
    (n (A ∩ C)).toReal + (n (A \ C)).toReal =
      (n A).toReal := by
  have hSplit : n (A ∩ C) + n (A \ C) = n A :=
    measure_inter_add_diff A hC
  have hFirst : n (A ∩ C) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ne_of_lt hFinite)
    exact measure_mono Set.inter_subset_left
  have hSecond : n (A \ C) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ne_of_lt hFinite)
    exact measure_mono Set.diff_subset
  refine ⟨hSplit, ?_⟩
  rw [← hSplit]
  exact (ENNReal.toReal_add hFirst hSecond).symm
