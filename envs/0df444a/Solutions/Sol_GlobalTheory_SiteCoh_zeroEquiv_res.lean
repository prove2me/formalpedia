-- Prove2me | solution 1 for GlobalTheory.SiteCoh.zeroEquiv_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:16:01.897379+00:00
-- url     : https://prove2.me/submissions/ecacbbe1-2ca6-43f2-82f4-c56b0f3ad2d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf
import Theorems.Thm_GlobalTheory_SiteCoh_freeSheafHomEquiv_map_comp
import Theorems.Thm_GlobalTheory_SiteCoh_extEquiv_res
import Theorems.Thm_P2M_GlobalTheory_SiteCoh_zeroEquiv_mk__3c6a869cada8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Opposite Limits Abelian
universe w v u
noncomputable section
open GlobalTheory GlobalTheory.SiteCoh
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
namespace GlobalTheory.SiteCoh
theorem _root_.solution (F : Sheaf J AddCommGrpCat.{v}) {U V : C} (i : V ⟶ U) (x : F.H' 0 U) :
    zeroEquiv F V (res F 0 i x) = F.obj.map i.op (zeroEquiv F U x) := by
  obtain ⟨y, rfl⟩ := (extEquiv F 0 U).symm.surjective x
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  rw [zeroEquiv_mk₀, ← freeSheafHomEquiv_map_comp, ← zeroEquiv_mk₀]
  congr 1
  apply (extEquiv F 0 V).injective
  rw [extEquiv_res, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, Ext.mk₀_comp_mk₀]
end GlobalTheory.SiteCoh
