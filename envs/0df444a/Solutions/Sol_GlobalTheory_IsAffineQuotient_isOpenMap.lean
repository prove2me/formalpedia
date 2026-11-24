-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.isOpenMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:32:42.340556+00:00
-- url     : https://prove2.me/submissions/4e0afd39-8e92-4c6d-a3a1-f5b90bc44844

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor



set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y Z : Scheme.{u}}
open GlobalTheory.IsAffineQuotient
variable {ρ : G →* Aut X} {π : X ⟶ Y}
variable (h : IsAffineQuotient ρ π)
include h
variable [Finite G]
namespace GlobalTheory.IsAffineQuotient
theorem _root_.solution : IsOpenMap π := fun U hU ↦ by
  rw [← h.isQuotientMap.isOpen_preimage]
  have : π ⁻¹' (π '' U) = ⋃ g, (ρ g).hom ⁻¹' U := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    refine ⟨fun ⟨y, hy, e⟩ ↦ ?_, fun ⟨g, hg⟩ ↦ ⟨_, hg, ((h.apply_eq_iff _ _).mpr ⟨g, rfl⟩).symm⟩⟩
    obtain ⟨g, rfl⟩ := (h.apply_eq_iff _ _).mp e.symm
    exact ⟨g, hy⟩
  rw [this]
  exact isOpen_iUnion fun g ↦ hU.preimage (ρ g).hom.continuous
end GlobalTheory.IsAffineQuotient
