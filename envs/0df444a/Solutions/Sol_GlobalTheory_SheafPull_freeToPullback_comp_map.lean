-- Prove2me | solution 1 for GlobalTheory.SheafPull.freeToPullback_comp_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:47:03.852394+00:00
-- url     : https://prove2.me/submissions/0adce1b9-aac2-426a-9d86-3c671fbbc4b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Theorems.Thm_GlobalTheory_SheafLES_freeYonedaHomEquiv_map_comp
import Theorems.Thm_GlobalTheory_SheafLES_map_comp


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
namespace GlobalTheory.SheafPull
theorem _root_.solution {V V' : C} {W : D} (i : W ⟶ p.obj V') (k : V' ⟶ V) :
    freeToPullback J K p i ≫ (p.sheafPullback AddCommGrpCat.{v} J K).map ((freeYoneda J).map k) =
      freeToPullback J K p (i ≫ p.map k) := by
  apply (freeYonedaHomEquiv W _).injective
  rw [freeYonedaHomEquiv_comp, freeToPullback, freeToPullback, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  have hu : ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app
        ((freeYoneda J).obj V)).hom.app (op V') (((freeYoneda J).map k).hom.app (op V') (tautSection V')) =
      ((p.sheafPullback AddCommGrpCat.{v} J K).map ((freeYoneda J).map k)).hom.app (op (p.obj V'))
        (((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app
          ((freeYoneda J).obj V')).hom.app (op V') (tautSection V')) :=
    congrArg (fun f => f.hom.app (op V') (tautSection V'))
      ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.naturality ((freeYoneda J).map k))
  have ht : ((freeYoneda J).map k).hom.app (op V') (tautSection V') =
      ((freeYoneda J).obj V).obj.map k.op (tautSection V) := by
    rw [← freeYonedaHomEquiv_apply, ← Category.comp_id ((freeYoneda J).map k),
      freeYonedaHomEquiv_map_comp]
    rfl
  have e2 := NatTrans.naturality_apply
    ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app ((freeYoneda J).obj V)).hom k.op
    (tautSection V)
  have e3 := hu.symm.trans ((congrArg (fun z => ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app
    ((freeYoneda J).obj V)).hom.app (op V') z) ht).trans e2)
  refine (NatTrans.naturality_apply _ i.op _).trans ?_
  refine (congrArg (fun z => (((p.sheafPullback AddCommGrpCat.{v} J K).obj
    ((freeYoneda J).obj V)).obj.map i.op) z) e3).trans ?_
  rw [op_comp, Functor.map_comp]
  rfl
end GlobalTheory.SheafPull
