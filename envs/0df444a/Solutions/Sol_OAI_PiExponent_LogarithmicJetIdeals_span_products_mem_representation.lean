-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.span_products_mem_representation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T19:07:56.798986+00:00
-- url     : https://prove2.me/submissions/556d1d76-9554-49f4-a5bb-a5dd2da0821d

import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators

theorem solution
    {A : Type*} [CommSemiring A] (I : Ideal A) (n : ℕ) (P : A)
    (hP : P ∈ Ideal.span
      {x : A | ∃ f : Fin n → A, (∀ i, f i ∈ I) ∧ x = ∏ i, f i}) :
    ∃ s : Finset (A × (Fin n → A)),
      P = ∑ z ∈ s, z.1 * ∏ i, z.2 i ∧
      ∀ z ∈ s, ∀ i, z.2 i ∈ I := by
  classical
  let ι := {f : Fin n → A // ∀ i, f i ∈ I}
  let g : ι → A := fun f => ∏ i, f.1 i
  have hgen :
      {x : A | ∃ f : Fin n → A, (∀ i, f i ∈ I) ∧ x = ∏ i, f i} = Set.range g := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩
    · rintro ⟨f, rfl⟩
      exact ⟨f.1, f.2, rfl⟩
  rw [hgen] at hP
  rcases (Finsupp.mem_ideal_span_range_iff_exists_finsupp).mp hP with ⟨c, hc⟩
  let φ : ι → A × (Fin n → A) := fun f => (c f, f.1)
  let s : Finset (A × (Fin n → A)) := c.support.image φ
  have hinj : Set.InjOn φ c.support := by
    intro f hf f' hf' heq
    apply Subtype.ext
    exact congrArg Prod.snd heq
  have hc' : (∑ f ∈ c.support, c f * ∏ i, f.1 i) = P := by
    simpa [Finsupp.sum, g] using hc
  refine ⟨s, ?_, ?_⟩
  · calc
      P = ∑ f ∈ c.support, c f * ∏ i, f.1 i := hc'.symm
      _ = ∑ z ∈ s, z.1 * ∏ i, z.2 i := by
        symm
        simp only [s, Finset.sum_image hinj, φ, Prod.fst, Prod.snd]
  · intro z hz i
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hz
    exact f.2 i