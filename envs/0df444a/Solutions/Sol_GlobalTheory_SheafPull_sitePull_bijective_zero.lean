-- Prove2me | solution 1 for GlobalTheory.SheafPull.sitePull_bijective_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:48.525929+00:00
-- url     : https://prove2.me/submissions/dec43c7c-5c12-430f-8a64-eff8d9b2292a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Theorems.Thm_GlobalTheory_SheafPull_equivZero_sitePull

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
    {V : C} {W : D} (i : W ⟶ p.obj V)
    (h : Function.Bijective fun s : F.obj.obj (op V) ↦ G.obj.map i.op (φ.hom.app (op V) s)) :
    Function.Bijective (sitePull.{w, w'} p φ 0 i) := by
  have key : ⇑(equivZero G W) ∘ ⇑(sitePull.{w, w'} p φ 0 i) =
      (fun s : F.obj.obj (op V) ↦ G.obj.map i.op (φ.hom.app (op V) s)) ∘ ⇑(equivZero F V) :=
    funext (equivZero_sitePull p φ i)
  have hb := h.comp (equivZero F V).bijective
  rw [← key] at hb
  exact (EquivLike.comp_bijective _ (equivZero G W)).1 hb
end GlobalTheory.SheafPull
