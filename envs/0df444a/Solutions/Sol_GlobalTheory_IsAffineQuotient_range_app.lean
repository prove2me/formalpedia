-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.range_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:56:19.862691+00:00
-- url     : https://prove2.me/submissions/a49c672e-69ed-485a-b81c-d58b98d543b2

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
namespace GlobalTheory.IsAffineQuotient
theorem _root_.solution (W : Y.Opens) :
    Set.range (π.app W) = {s | IsInvariantSection ρ (π ⁻¹ᵁ W) s} :=
  Set.ext fun s ↦ ⟨by rintro ⟨t, rfl⟩; exact isInvariantSection_app ρ π h.comp_eq W t,
    h.mem_range_app W s⟩
end GlobalTheory.IsAffineQuotient
