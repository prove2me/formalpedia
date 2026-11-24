-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.quasiCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:35:07.732573+00:00
-- url     : https://prove2.me/submissions/70ef0609-c0b1-4cad-850a-1df486803b97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv

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
variable {S : Scheme.{u}} (q : Y ⟶ S)
namespace GlobalTheory.IsAffineQuotient
theorem _root_.solution [QuasiCompact (π ≫ q)] : QuasiCompact q := ⟨fun U hU hU' ↦ by
  have := h.surjective
  rw [← π.surjective.image_preimage (q ⁻¹' U)]
  exact (QuasiCompact.isCompact_preimage (f := π ≫ q) U hU hU').image π.continuous⟩
end GlobalTheory.IsAffineQuotient
