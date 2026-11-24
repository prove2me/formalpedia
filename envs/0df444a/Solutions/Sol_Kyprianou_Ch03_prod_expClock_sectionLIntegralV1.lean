-- Prove2me | solution 1 for Kyprianou.Ch03.prod_expClock_sectionLIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:42:51.274655+00:00
-- url     : https://prove2.me/submissions/2a1f5415-9c43-4303-8e14-3318b14c4934

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_expClockRationalBetweenV1
import Theorems.Thm_Kyprianou_Ch03_prod_countable_measurable_left_rectanglesV1
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega OmegaE : Type} [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (tau : Omega → WithTop NNReal) (htau : Measurable tau)
    (e : OmegaE → NNReal) :
    (P.prod Q) {z : Omega × OmegaE | tau z.1 < (e z.2 : WithTop NNReal)} =
      ∫⁻ w, Q {z : OmegaE | tau w < (e z : WithTop NNReal)} ∂P := by
  let A (r : ℚ) := {w : Omega | tau w < ((r : ℝ).toNNReal : WithTop NNReal)}
  let B (r : ℚ) := {z : OmegaE | (r : ℝ).toNNReal < e z}
  have hA (r : ℚ) : MeasurableSet (A r) := measurableSet_lt htau measurable_const
  have hS : {z : Omega × OmegaE | tau z.1 < (e z.2 : WithTop NNReal)} =
      ⋃ r, A r ×ˢ B r := by
    ext z
    simp only [mem_setOf_eq, mem_iUnion, mem_prod, A, B]
    exact Kyprianou.Ch03.expClockRationalBetweenV1 (tau z.1) (e z.2)
  rw [hS, Kyprianou.Ch03.prod_countable_measurable_left_rectanglesV1 P Q A B hA]
  apply lintegral_congr
  intro w
  congr 1
  ext z
  simp only [mem_iUnion, mem_setOf_eq, B]
  constructor
  · rintro ⟨r, hr⟩
    exact (Kyprianou.Ch03.expClockRationalBetweenV1 (tau w) (e z)).mpr
      ⟨r.1, r.2, hr⟩
  · intro h
    obtain ⟨r, hr, hrz⟩ :=
      (Kyprianou.Ch03.expClockRationalBetweenV1 (tau w) (e z)).mp h
    exact ⟨⟨r, hr⟩, hrz⟩
