-- Prove2me | solution 1 for Kyprianou.Ch04.zeroTimeRestrictionIccIocV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:19:15.246796+00:00
-- url     : https://prove2.me/submissions/70ff2fe7-ec85-4dfa-8c1b-9ba60c8fb741

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The closed and left-open windows give the same measure when there is no initial atom. -/
theorem solution (μ : Measure (ℝ × ℝ))
    (hzero : μ (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0)
    (t : ℝ) (B : Set ℝ) :
    μ.restrict (Icc 0 t ×ˢ B) = μ.restrict (Ioc 0 t ×ˢ B) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null _ hzero
    intro p hp
    obtain ⟨⟨ht, hB⟩, hnot⟩ := hp
    have hnotpos : ¬ 0 < p.1 := fun h => hnot ⟨⟨h, ht.2⟩, hB⟩
    exact ⟨le_antisymm (le_of_not_gt hnotpos) ht.1, Set.mem_univ _⟩
  · rw [sdiff_eq_empty.mpr (Set.prod_mono Ioc_subset_Icc_self (Subset.rfl))]
    exact measure_empty
