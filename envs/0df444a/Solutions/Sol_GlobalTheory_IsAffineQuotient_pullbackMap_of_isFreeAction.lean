-- Prove2me | solution 1 for GlobalTheory.IsAffineQuotient.pullbackMap_of_isFreeAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:57:34.335501+00:00
-- url     : https://prove2.me/submissions/98ce753a-6ad7-4089-ba43-115d7871ee3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_IsAffineQuotient_of_isPullback_of_isFreeAction
import Theorems.Thm_GlobalTheory_pullbackAction_fst
import Theorems.Thm_GlobalTheory_pullbackAction_snd
import Theorems.Thm_GlobalTheory_isPullback_pullbackMap
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor


attribute [reassoc (attr := simp)] GlobalTheory.pullbackAction_fst
attribute [reassoc (attr := simp)] GlobalTheory.pullbackAction_snd

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y X' Y' S S' : Scheme.{u}}
attribute [local simp] pullback.map pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable (ρ : G →* Aut X) (f : X ⟶ S) (hf : ∀ g, (ρ g).hom ≫ f = f) (t : S' ⟶ S)
variable {ρ f} [Finite G] {π : X ⟶ Y} (h : IsAffineQuotient ρ π) (q : Y ⟶ S) (hq : π ≫ q = f)
include h
namespace GlobalTheory
namespace IsAffineQuotient
theorem _root_.solution (hρ : IsFreeAction ρ) :
    IsAffineQuotient (pullbackAction ρ f hf t)
      (pullback.map f t q t π (𝟙 _) (𝟙 _) (by simp [hq]) (by simp)) :=
  h.of_isPullback_of_isFreeAction (isPullback_pullbackMap f t π q hq) (by simp) (fun g ↦ by
    apply pullback.hom_ext <;> simp [h.comp_eq]) hρ
end IsAffineQuotient
end GlobalTheory
