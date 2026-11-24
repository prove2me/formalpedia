-- Prove2me | solution 1 for GlobalTheory.SheafPull.res_sitePull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:02:44.731475+00:00
-- url     : https://prove2.me/submissions/0a6889f1-81d9-48ab-a92e-b1a060be9ab2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Theorems.Thm_GlobalTheory_SheafPull_comp_extMap_left
import Theorems.Thm_GlobalTheory_SheafPull_map_comp_freeToPullback
import Theorems.Thm_GlobalTheory_SheafLES_res_apply


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
    (n : ℕ) {V : C} {W W' : D} (i : W ⟶ p.obj V) (k : W' ⟶ W) (x : Sheaf.H'.{w} F n V) :
    res G n k (sitePull.{w, w'} p φ n i x) = sitePull.{w, w'} p φ n (k ≫ i) x := by
  have h1 := comp_extMap_left (p.sheafPullback AddCommGrpCat.{v} J K) (freeToPullback J K p i)
    (((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ) ((freeYoneda K).map k) n x
  rw [map_comp_freeToPullback] at h1
  exact (res_apply n k _).trans h1
end GlobalTheory.SheafPull
