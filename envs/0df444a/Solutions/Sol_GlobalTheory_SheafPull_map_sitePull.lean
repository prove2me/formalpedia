-- Prove2me | solution 1 for GlobalTheory.SheafPull.map_sitePull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:01:33.175216+00:00
-- url     : https://prove2.me/submissions/688ef8ca-0c0a-4282-9810-cf6db83a7f9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Theorems.Thm_GlobalTheory_SheafPull_comp_extMap_right
import Theorems.Thm_GlobalTheory_SheafLES_map_apply


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
    (t : G ⟶ G') (n : ℕ) {V : C} {W : D} (i : W ⟶ p.obj V) (x : Sheaf.H'.{w} F n V) :
    map t n W (sitePull.{w, w'} p φ n i x) = sitePull.{w, w'} p
      (φ ≫ (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).map t) n i x := by
  have h1 := comp_extMap_right (p.sheafPullback AddCommGrpCat.{v} J K) (freeToPullback J K p i)
    (((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ) t n x
  rw [← Adjunction.homEquiv_naturality_right_symm] at h1
  exact (map_apply t n W _).trans h1
end GlobalTheory.SheafPull
