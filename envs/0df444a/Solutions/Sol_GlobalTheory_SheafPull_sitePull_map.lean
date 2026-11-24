-- Prove2me | solution 1 for GlobalTheory.SheafPull.sitePull_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:01:39.693827+00:00
-- url     : https://prove2.me/submissions/bb74f8cf-c8c7-4268-b6bd-39e128340213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Theorems.Thm_GlobalTheory_SheafPull_extMap_comp_right
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
theorem _root_.solution (φ : F' ⟶ (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj G)
    (s : F ⟶ F') (n : ℕ) {V : C} {W : D} (i : W ⟶ p.obj V) (x : Sheaf.H'.{w} F n V) :
    sitePull.{w, w'} p φ n i (map s n V x) = sitePull.{w, w'} p (s ≫ φ) n i x := by
  have h1 := extMap_comp_right (p.sheafPullback AddCommGrpCat.{v} J K) (freeToPullback J K p i)
    (((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ) s n x
  rw [← Adjunction.homEquiv_naturality_left_symm] at h1
  exact (congrArg (fun y => sitePull.{w, w'} p φ n i y) (map_apply s n V x)).trans h1
end GlobalTheory.SheafPull
