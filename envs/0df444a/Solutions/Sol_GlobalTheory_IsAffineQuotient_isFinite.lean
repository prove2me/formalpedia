-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.isFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:32:41.38034+00:00
-- url     : https://prove2.me/submissions/7867e6a4-c7da-4bfb-ae40-572952ca1221

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
theorem _root_.solution [LocallyOfFiniteType (π ≫ q)] : IsFinite π :=
  have := h.isIntegralHom
  have : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π q
  (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType π).mpr ⟨‹_›, ‹_›⟩
end GlobalTheory.IsAffineQuotient
