-- Prove2me | solution 1 for GlobalTheory.SheafLES.equivZero_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:00.482549+00:00
-- url     : https://prove2.me/submissions/eb2d04cf-05e8-47fd-b158-5c976af63754

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_GlobalTheory_SheafLES_freeYonedaHomEquiv_map_comp
import Theorems.Thm_GlobalTheory_SheafLES_res_apply
import Theorems.Thm_P2M_GlobalTheory_SheafLES_equivZero_mk__f9955a9468d8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
variable {F G K : Sheaf J AddCommGrpCat.{v}}
namespace GlobalTheory.SheafLES
theorem _root_.solution {U V : C} (i : V ⟶ U) (x : Sheaf.H'.{w'} F 0 U) :
    equivZero F V (res F 0 i x) = F.obj.map i.op (equivZero F U x) := by
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective ((freeYoneda J).obj U) F).surjective x
  rw [res_apply, Ext.mk₀_comp_mk₀, equivZero_mk₀, equivZero_mk₀, freeYonedaHomEquiv_map_comp]
end GlobalTheory.SheafLES
