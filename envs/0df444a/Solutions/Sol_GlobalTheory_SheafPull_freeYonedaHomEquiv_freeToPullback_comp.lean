-- Prove2me | solution 1 for GlobalTheory.SheafPull.freeYonedaHomEquiv_freeToPullback_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:47:04.902919+00:00
-- url     : https://prove2.me/submissions/dec8118a-a7f8-4297-915e-eeceabe4bc50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp

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
theorem _root_.solution {V : C} {W : D} (i : W ⟶ p.obj V)
    {G : Sheaf K AddCommGrpCat.{v}}
    (b : (p.sheafPullback AddCommGrpCat.{v} J K).obj ((freeYoneda J).obj V) ⟶ G) :
    freeYonedaHomEquiv W G (freeToPullback J K p i ≫ b) =
      G.obj.map i.op (freeYonedaHomEquiv V _
        ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _ b)) := by
  rw [freeYonedaHomEquiv_comp, freeToPullback, Equiv.apply_symm_apply, Adjunction.homEquiv_unit,
    freeYonedaHomEquiv_apply]
  exact NatTrans.naturality_apply b.hom i.op _
end GlobalTheory.SheafPull
