-- Prove2me | solution 1 for GlobalTheory.DenseClosedAffineSubsets.exists_closed_affineSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:10:48.558387+00:00
-- url     : https://prove2.me/submissions/5ec5ff05-6c4c-4bb4-bbd3-7a1eab503099

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets
namespace GlobalTheory.DenseClosedAffineSubsets
theorem _root_.solution {U S : Scheme.{0}} [IsAffine U] [IsAffine S] (u : U ⟶ S)
    [LocallyOfFiniteType u] :
    ∃ (σ : Type) (_ : Fintype σ) (g : σ → Γ(U, ⊤)),
      IsClosedImmersion (AffineSpace.homOfVector u g) := by
  have h : u.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  letI := u.appTop.hom.toAlgebra
  obtain ⟨t, ht⟩ := h.out
  refine ⟨t, inferInstance, fun a ↦ a.1, IsClosedImmersion.of_surjective_of_isAffine _ ?_⟩
  intro x
  have hx : x ∈ Algebra.adjoin Γ(S, ⊤) (t : Set Γ(U, ⊤)) := ht ▸ trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨_, AffineSpace.homOfVector_appTop_coord u (fun a : t ↦ a.1) ⟨x, hx⟩⟩
  | algebraMap r =>
    refine ⟨(𝔸(t; S) ↘ S).appTop r, ?_⟩
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over]
    rfl
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, map_mul _ _ _⟩
end GlobalTheory.DenseClosedAffineSubsets
