-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_span_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:50:33.425341+00:00
-- url     : https://prove2.me/submissions/6a0cee2d-480a-4e0b-9e5f-3da357fa8d38

import Mathlib
open scoped BigOperators

theorem solution
    {R α : Type} [CommRing R] [IsNoetherianRing R]
    (F : α → R) :
    ∃ m : Nat, ∃ idx : Fin m → α,
      Ideal.span (Set.range (fun j : Fin m => F (idx j))) =
        Ideal.span (Set.range F) := by
  classical
  obtain ⟨M, ⟨s, rfl⟩, hM⟩ := set_has_maximal_iff_noetherian.mpr inferInstance
    (Set.range (fun s : Finset α => Ideal.span (F '' (s : Set α)))) ⟨_, ⟨∅, rfl⟩⟩
  have hle : Ideal.span (Set.range F) ≤ Ideal.span (F '' (s : Set α)) := by
    rw [Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    by_contra hna
    apply hM _ ⟨insert a s, rfl⟩
    refine lt_of_le_of_ne (Ideal.span_mono (Set.image_mono (by simp))) ?_
    intro heq
    apply hna
    have heq' : Ideal.span (F '' (s : Set α)) =
        Ideal.span (F '' ((insert a s : Finset α) : Set α)) := heq
    rw [heq']
    exact Ideal.subset_span ⟨a, by simp, rfl⟩
  refine ⟨s.card, fun j => (s.equivFin.symm j).1, le_antisymm ?_ ?_⟩
  · exact Ideal.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨_, rfl⟩)
  · refine hle.trans (Ideal.span_mono ?_)
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨s.equivFin ⟨a, ha⟩, by simp⟩
