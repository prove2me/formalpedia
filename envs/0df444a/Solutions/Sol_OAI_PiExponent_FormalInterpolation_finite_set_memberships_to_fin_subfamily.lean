-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_set_memberships_to_fin_subfamily
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:43:50.147606+00:00
-- url     : https://prove2.me/submissions/5fadecbe-57b4-4bd4-9958-f947ed145eee

import Mathlib.RingTheory.Ideal.Operations

open Set

theorem solution
    {R α ι : Type} [CommSemiring R] [Fintype α]
    (x : α → R) (g : ι → R)
    (h : ∀ a, ∃ s : Finset ι, x a ∈ Ideal.span (g '' (s : Set ι))) :
    ∃ n : Nat, ∃ f : Fin n → ι,
      ∀ a, x a ∈ Ideal.span (Set.range (fun j => g (f j))) := by
  classical
  let s : α → Finset ι := fun a => Classical.choose (h a)
  have hs : ∀ a, x a ∈ Ideal.span (g '' (s a : Set ι)) :=
    fun a => Classical.choose_spec (h a)
  let S : Finset ι := Finset.univ.biUnion s
  have hsS : ∀ a, x a ∈ Ideal.span (g '' (S : Set ι)) := by
    intro a
    have hsubset : g '' (s a : Set ι) ⊆ g '' (S : Set ι) := by
      rintro y ⟨i, hi, rfl⟩
      refine ⟨i, ?_, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hi⟩
    exact (Ideal.span_mono hsubset) (hs a)
  let e : {i // i ∈ S} ≃ Fin S.card := S.equivFin
  let f : Fin S.card → ι := fun j => (e.symm j).val
  have hrange : Set.range f = (S : Set ι) := by
    ext i
    constructor
    · rintro ⟨j, rfl⟩
      exact (e.symm j).property
    · intro hi
      refine ⟨e ⟨i, hi⟩, ?_⟩
      simp [f]
  have hgen : Set.range (fun j : Fin S.card => g (f j)) = g '' (S : Set ι) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨f j, ?_, rfl⟩
      rw [← hrange]
      exact ⟨j, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      have hi' : i ∈ Set.range f := by
        rw [hrange]
        exact hi
      rcases hi' with ⟨j, rfl⟩
      exact ⟨j, rfl⟩
  refine ⟨S.card, f, ?_⟩
  intro a
  rw [hgen]
  exact hsS a