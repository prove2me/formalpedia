-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.isNormalScheme
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:19:56.814868+00:00
-- url     : https://prove2.me/submissions/a3e49e83-55f6-4d1b-a8ea-8a164c7ff2b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_localization_of_isInvariant
import Theorems.Thm_GlobalTheory_IsNormalScheme_iff_forall_isAffineOpen


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
theorem _root_.solution [IsNormalScheme X] : IsNormalScheme Y :=
  (IsNormalScheme.iff_forall_isAffineOpen Y).mpr fun W hW p _ ↦ by
    have := h.isAffineHom
    let := sectionsAction ρ _ (h.preimage_le W)
    let := (π.app W).hom.toAlgebra
    obtain ⟨_, _, _⟩ := h.isInvariant W
    exact isDomain_and_isIntegrallyClosed_localization_of_isInvariant G Γ(X, π ⁻¹ᵁ W) Γ(Y, W)
      ((IsNormalScheme.iff_forall_isAffineOpen X).mp ‹_› _ (hW.preimage π)) p
end GlobalTheory.IsAffineQuotient
