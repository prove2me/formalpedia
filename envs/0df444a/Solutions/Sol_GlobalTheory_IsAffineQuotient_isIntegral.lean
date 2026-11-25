-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:01:45.441618+00:00
-- url     : https://prove2.me/submissions/9b2af0b8-2c9e-4001-8247-a91bcc4bd893

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_IsAffineQuotient_isReduced

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
theorem _root_.solution [IsIntegral X] : IsIntegral Y :=
  have := h.isReduced
  have := h.surjective
  have : IrreducibleSpace Y := π.surjective.irreducibleSpace π.continuous
  isIntegral_of_irreducibleSpace_of_isReduced Y
end GlobalTheory.IsAffineQuotient
