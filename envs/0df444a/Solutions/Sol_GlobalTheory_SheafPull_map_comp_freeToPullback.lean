-- Prove2me | solution 1 for GlobalTheory.SheafPull.map_comp_freeToPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:47:05.719042+00:00
-- url     : https://prove2.me/submissions/ec622778-a8b3-4713-bab9-852ef1cc2b8b

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
theorem _root_.solution {V : C} {W W' : D} (i : W ⟶ p.obj V) (k : W' ⟶ W) :
    (freeYoneda K).map k ≫ freeToPullback J K p i = freeToPullback J K p (k ≫ i) := by
  apply (freeYonedaHomEquiv W' _).injective
  rw [freeYonedaHomEquiv_map_comp, freeToPullback, freeToPullback, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, op_comp, Functor.map_comp]
  rfl
end GlobalTheory.SheafPull
