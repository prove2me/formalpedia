-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.mem_ideal_span_range_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:44:38.255528+00:00
-- url     : https://prove2.me/submissions/a35600bd-699c-4caa-9b0f-9239e06802b2

import Mathlib.RingTheory.Ideal.Operations

theorem solution
    {R ι : Type} [CommSemiring R]
    (g : ι → R) (x : R)
    (hx : x ∈ Ideal.span (Set.range g)) :
    ∃ s : Finset ι, x ∈ Ideal.span (g '' (s : Set ι)) := by
  classical
  change x ∈ Submodule.span R (Set.range g) at hx
  obtain ⟨t, ht, hxt⟩ := Submodule.mem_span_finite_of_mem_span hx
  let s : Finset ι := t.attach.image (fun y => Classical.choose (ht y.property))
  refine ⟨s, ?_⟩
  apply Submodule.span_mono ?_ hxt
  intro y hy
  let i := Classical.choose (ht hy)
  have hi : g i = y := Classical.choose_spec (ht hy)
  have his : i ∈ s := by
    dsimp [s]
    exact Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_attach t ⟨y, hy⟩, rfl⟩
  exact ⟨i, his, hi⟩