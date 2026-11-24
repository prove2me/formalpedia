-- Prove2me | solution 1 for GlobalTheory.isPullback_pullbackMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:07:15.435698+00:00
-- url     : https://prove2.me/submissions/df1db5b5-2ade-4566-a096-e1903b220fd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_pullbackAction_fst
import Theorems.Thm_GlobalTheory_pullbackAction_snd
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
namespace GlobalTheory
theorem _root_.solution (π : X ⟶ Y) (q : Y ⟶ S) (hq : π ≫ q = f) :
    IsPullback (pullback.fst f t)
      (pullback.map f t q t π (𝟙 _) (𝟙 _) (by simp [hq]) (by simp)) π (pullback.fst q t) :=
  .of_bot (by simpa [hq] using IsPullback.of_hasPullback f t) (by simp) (.of_hasPullback q t)
end GlobalTheory
