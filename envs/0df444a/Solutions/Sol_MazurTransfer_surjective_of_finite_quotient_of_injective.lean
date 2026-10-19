-- Prove2me | solution 1 for MazurTransfer.surjective_of_finite_quotient_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-16T11:31:16.498258+00:00
-- url     : https://prove2.me/submissions/58d3afce-304a-47c8-9b30-3d8c4b198eaa

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: finite-index subgroup criterion for an injective group
endomorphism to be surjective. Named downstream consumer: the original
pi norm map on decomposition-fixed points at thirteen. -/
import Mathlib

theorem solution (A : Type) [CommGroup A] (f : A →* A) (U : Subgroup A)
    [Finite (A ⧸ U)] (hU : U ≤ U.comap f)
    (hs : ∀ u ∈ U, ∃ v ∈ U, f v = u)
    (hi : Function.Injective f) : Function.Surjective f := by
  let qf : A ⧸ U →* A ⧸ U := QuotientGroup.map U U f hU
  have hker : ∀ x : A ⧸ U, qf x = 1 → x = 1 := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    intro ha
    have hfa : f a ∈ U := (QuotientGroup.eq_one_iff (f a)).mp ha
    obtain ⟨u, hu, he⟩ := hs (f a) hfa
    have hau : a = u := hi he.symm
    exact (QuotientGroup.eq_one_iff a).mpr (hau.symm ▸ hu)
  have hqi : Function.Injective qf := by
    intro x y hxy
    apply div_eq_one.mp
    apply hker
    rw [map_div, hxy, div_self']
  have hqs : Function.Surjective qf := Finite.surjective_of_injective hqi
  intro a
  obtain ⟨x, hx⟩ := hqs (QuotientGroup.mk a)
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
  have hx' : (QuotientGroup.mk (f b) : A ⧸ U) = QuotientGroup.mk a := hx
  have hd : a / f b ∈ U := (QuotientGroup.eq_one_iff (a / f b)).mp (by
    rw [QuotientGroup.mk_div, hx', div_self'])
  obtain ⟨u, hu, he⟩ := hs (a / f b) hd
  refine ⟨u * b, ?_⟩
  rw [map_mul, he, div_mul_cancel]

#print axioms solution
