-- Prove2me | solution 1 for MazurTransfer.locally_standardSmooth_relativeDimension_one_of_kaehler_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T04:55:26.865521+00:00
-- url     : https://prove2.me/submissions/2f0f0ba0-c0e8-4a4d-8b1e-f433c4af2a29

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: relative dimension one from genuine Kaehler differentials
for smooth domain algebras. Named downstream consumer: the actual order-thirteen
chart morphisms. This uses genuine localization of the differential module.
-/
import Mathlib

noncomputable section
open Module

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]

theorem solution
    [Algebra.Smooth R S] (he : Nonempty (Ω[S⁄R] ≃ₗ[S] S)) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap R S) := by
  classical
  obtain ⟨e⟩ := he
  let b : Basis Unit S Ω[S⁄R] := (Basis.singleton Unit S).map e.symm
  obtain ⟨s, hs, h⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R S
  have hs' : Ideal.span {x : S | x ∈ s ∧ x ≠ 0} = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Ideal.span_le.mpr
    intro x hx
    by_cases hz : x = 0
    · subst x
      exact Ideal.zero_mem _
    · exact Ideal.subset_span ⟨hx, hz⟩
  refine ⟨_, hs', fun x hx ↦ ?_⟩
  let T := Localization.Away x
  have : IsDomain T := Localization.Away.isDomain hx.2
  have : Algebra.IsStandardSmooth R T := h x hx.1
  let bT : Basis Unit T Ω[T⁄R] := b.ofIsLocalizedModule T (Submonoid.powers x)
    (KaehlerDifferential.map R R S T)
  rw [← IsScalarTower.algebraMap_eq R S T]
  change RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap R T)
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  apply (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth 1).mpr
  simp only [rank_eq_card_basis bT, Cardinal.mk_fintype, Fintype.card_unique,
    Nat.cast_one]


#print axioms solution
