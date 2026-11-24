-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovCountableFibreMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:07:05.229402+00:00
-- url     : https://prove2.me/submissions/a0cd3965-f2fc-4fab-b1b9-9b71e7743cc1

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Omega I E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (T : Omega → I) (hCount : Countable (Set.range T))
    (hFib : ∀ i : I, MeasurableSet {w | T w = i})
    (Y : I → Omega → E) (hY : ∀ i, Measurable (Y i)) :
    Measurable (fun w => Y (T w) w) := by
  classical
  letI : Countable (Set.range T) := hCount
  intro S hS
  have he : (fun w => Y (T w) w) ⁻¹' S =
      ⋃ i : Set.range T, {w | T w = (i : I)} ∩ Y (i : I) ⁻¹' S := by
    ext w
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hw
      exact ⟨⟨T w, ⟨w, rfl⟩⟩, rfl, hw⟩
    · rintro ⟨i, hi, hw⟩
      rw [hi]
      exact hw
  rw [he]
  exact MeasurableSet.iUnion fun i => (hFib i).inter (hY i hS)
