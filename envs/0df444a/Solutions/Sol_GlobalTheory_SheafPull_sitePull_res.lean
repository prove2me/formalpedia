-- Prove2me | solution 1 for GlobalTheory.SheafPull.sitePull_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:01:32.163865+00:00
-- url     : https://prove2.me/submissions/a6356e1c-32a1-4bcb-9dc0-76edadae0a9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Theorems.Thm_GlobalTheory_SheafPull_extMap_comp_left
import Theorems.Thm_GlobalTheory_SheafPull_freeToPullback_comp_map
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
    (n : ℕ) {V V' : C} {W : D} (i : W ⟶ p.obj V') (k : V' ⟶ V) (x : Sheaf.H'.{w} F n V) :
    sitePull.{w, w'} p φ n i (res F n k x) = sitePull.{w, w'} p φ n (i ≫ p.map k) x := by
  have h1 := extMap_comp_left (p.sheafPullback AddCommGrpCat.{v} J K) (freeToPullback J K p i)
    (((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ) ((freeYoneda J).map k) n x
  rw [freeToPullback_comp_map] at h1
  exact (congrArg (fun y => sitePull.{w, w'} p φ n i y) (res_apply n k x)).trans h1
end GlobalTheory.SheafPull
