-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.isProper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:51:44.515557+00:00
-- url     : https://prove2.me/submissions/c06ea83e-11c0-430b-94ab-9331337d9350

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_IsAffineQuotient_locallyOfFiniteType
import Theorems.Thm_GlobalTheory_IsAffineQuotient_isSeparated

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
theorem _root_.solution [IsLocallyNoetherian S] [IsProper (π ≫ q)] : IsProper q :=
  have := h.surjective
  have := h.isSeparated q
  have := h.locallyOfFiniteType q
  have : UniversallyClosed q := .of_comp_surjective π q
  {}
end GlobalTheory.IsAffineQuotient
