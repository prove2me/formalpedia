-- Prove2me | solution 1 for GlobalTheory.SheafPull.equivZero_sitePull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:29.229182+00:00
-- url     : https://prove2.me/submissions/fb656071-58e8-49cd-88d3-fb5c55eb5c2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Theorems.Thm_P2M_GlobalTheory_SheafPull_extMap_mk__8ca0febd9656
import Theorems.Thm_GlobalTheory_SheafPull_freeYonedaHomEquiv_freeToPullback_comp
import Theorems.Thm_P2M_GlobalTheory_SheafLES_equivZero_mk__f9955a9468d8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w w' w'' v u u₁ v₁ u₂ v₂
noncomputable section
open GlobalTheory
open GlobalTheory.SheafPull
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  (p : C ⥤ D) [p.IsContinuous J K]
  [(p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]
open SheafLES
variable [PreservesFiniteLimits (p.sheafPullback AddCommGrpCat.{v} J K)]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{v})]
  {F F' : Sheaf J AddCommGrpCat.{v}} {G G' : Sheaf K AddCommGrpCat.{v}}
namespace GlobalTheory.SheafPull
theorem _root_.solution (φ : F ⟶ (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj G)
    {V : C} {W : D} (i : W ⟶ p.obj V) (x : Sheaf.H'.{w} F 0 V) :
    equivZero G W (sitePull.{w, w'} p φ 0 i x) =
      G.obj.map i.op (φ.hom.app (op V) (equivZero F V x)) := by
  obtain ⟨g, rfl⟩ : ∃ g, Ext.mk₀ g = x := ⟨Ext.addEquiv₀ x, Ext.mk₀_addEquiv₀_apply x⟩
  unfold sitePull
  erw [extMap_mk₀]
  rw [equivZero_mk₀, equivZero_mk₀, freeYonedaHomEquiv_freeToPullback_comp,
    Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply, freeYonedaHomEquiv_comp]
end GlobalTheory.SheafPull
