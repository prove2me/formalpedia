-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.exists_preimage_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:47:44.955406+00:00
-- url     : https://prove2.me/submissions/bac5567f-e4b9-48f7-bc2a-ab2156869f8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_IsAffineQuotient_isOpenMap

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
variable {G : Type v} [Group G] {X Y Z : Scheme.{u}}
open GlobalTheory.IsAffineQuotient
variable {ρ : G →* Aut X} {π : X ⟶ Y}
variable (h : IsAffineQuotient ρ π)
include h
variable [Finite G]
namespace GlobalTheory.IsAffineQuotient
theorem _root_.solution {U : X.Opens} (hU : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U) :
    ∃ W : Y.Opens, π ⁻¹ᵁ W = U := by
  refine ⟨⟨π '' U, h.isOpenMap _ U.isOpen⟩, le_antisymm ?_ fun x hx ↦ ⟨x, hx, rfl⟩⟩
  rintro x ⟨y, hy, e⟩
  obtain ⟨g, rfl⟩ := (h.apply_eq_iff _ _).mp e
  exact hU g hy
end GlobalTheory.IsAffineQuotient
