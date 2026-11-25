-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.finrank_of_isFreeAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:54:12.575209+00:00
-- url     : https://prove2.me/submissions/f1dec6b2-3ea6-43c7-b427-32f6d54b5ffe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_IsFreeAction_isFreeRingAction
import Theorems.Thm_GlobalTheory_isPullback_fromSpec_app
import Theorems.Thm_GlobalTheory_IsAffineQuotient_isFinite_of_isFreeAction
import Theorems.Thm_GlobalTheory_IsAffineQuotient_etale_of_isFreeAction
import Theorems.Thm_GlobalTheory_FreeQuotient_finite_and_projective
import Theorems.Thm_GlobalTheory_FreeQuotient_rankAtStalk_eq_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
open GlobalTheory.IsAffineQuotient
variable [Finite G] {ρ : G →* Aut X} {π : X ⟶ Y} (h : IsAffineQuotient ρ π) (hρ : IsFreeAction ρ)
include h hρ
namespace GlobalTheory.IsAffineQuotient
theorem _root_.solution (y : Y) : π.finrank y = Nat.card G := by
  have := h.isFinite_of_isFreeAction hρ
  have := h.etale_of_isFreeAction hρ
  obtain ⟨_, ⟨W, hW, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hW : IsAffineOpen W := hW
  let := sectionsAction ρ _ (h.preimage_le W)
  let := (π.app W).hom.toAlgebra
  obtain ⟨_, _, _⟩ := h.isInvariant W
  have hf := hρ.isFreeRingAction (hW.preimage π) (h.preimage_le W)
  obtain ⟨_, _⟩ := FreeQuotient.finite_and_projective Γ(Y, W) hf
  obtain ⟨z, rfl⟩ : y ∈ Set.range hW.fromSpec := by rwa [hW.range_fromSpec]
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _
    (isPullback_fromSpec_app π hW (hW.preimage π)),
    ← FreeQuotient.rankAtStalk_eq_card Γ(Y, W) hf z]
  exact Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, W) Γ(X, π ⁻¹ᵁ W) _
end GlobalTheory.IsAffineQuotient
