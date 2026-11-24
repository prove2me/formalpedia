-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.isFinite_of_isFreeAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:21:23.166891+00:00
-- url     : https://prove2.me/submissions/cd66802a-4cd5-4bf0-81e6-9d478f341a44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_IsFreeAction_isFreeRingAction
import Theorems.Thm_GlobalTheory_FreeQuotient_finite_and_projective


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
theorem _root_.solution : IsFinite π where
  toIsAffineHom := h.isAffineHom
  finite_app W hW := by
    have := h.isAffineHom
    let := sectionsAction ρ _ (h.preimage_le W)
    let := (π.app W).hom.toAlgebra
    obtain ⟨_, _, _⟩ := h.isInvariant W
    exact (FreeQuotient.finite_and_projective Γ(Y, W)
      (hρ.isFreeRingAction (hW.preimage π) (h.preimage_le W))).1
end GlobalTheory.IsAffineQuotient
