-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:29:34.46634+00:00
-- url     : https://prove2.me/submissions/b6faa65d-923c-476a-801c-908d977990ec

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
variable {S : Scheme.{u}} (q : Y ⟶ S)
namespace GlobalTheory.IsAffineQuotient
theorem _root_.solution [IsSeparated (π ≫ q)] : IsSeparated q := by
  have := h.surjective
  have := h.isIntegralHom
  let m : pullback (π ≫ q) (π ≫ q) ⟶ pullback q q :=
    pullback.map (π ≫ q) (π ≫ q) q q π π (𝟙 S) (by simp) (by simp)
  have : UniversallyClosed π := inferInstance
  have hm : UniversallyClosed m :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹_› ‹_› rfl rfl
  have e : π ≫ pullback.diagonal q = pullback.diagonal (π ≫ q) ≫ m := by
    apply pullback.hom_ext <;> simp [m, pullback.map, pullback.lift_fst, pullback.lift_snd]
  have : UniversallyClosed (π ≫ pullback.diagonal q) := by rw [e]; infer_instance
  have : UniversallyClosed (pullback.diagonal q) := UniversallyClosed.of_comp_surjective π _
  exact ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal q).isClosedMap.isClosed_range⟩
end GlobalTheory.IsAffineQuotient
