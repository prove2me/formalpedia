-- Prove2me | solution 1 for GlobalTheory.Flasque.sectionsEquiv_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:48:31.706689+00:00
-- url     : https://prove2.me/submissions/94c0d8e7-d005-40d1-9349-15e997cc43d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Theorems.Thm_GlobalTheory_Flasque_freeSheafHomEquiv_freeSheafMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w v u
open GlobalTheory
open GlobalTheory.Flasque
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
namespace GlobalTheory.Flasque
theorem _root_.solution (F : Sheaf J AddCommGrpCat.{v}) {V U : C} (i : V ⟶ U)
    (x : F.H' 0 U) :
    sectionsEquiv F V ((F.cohomologyPresheaf 0).map i.op x) =
      F.obj.map i.op (sectionsEquiv F U x) := by
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (freeSheaf J U) F).2 x
  refine (congrArg (sectionsEquiv F V) (Ext.mk₀_comp_mk₀ (freeSheafMap J i) g)).trans ?_
  rw [sectionsEquiv_mk₀, sectionsEquiv_mk₀, freeSheafHomEquiv_freeSheafMap_comp]
end GlobalTheory.Flasque
