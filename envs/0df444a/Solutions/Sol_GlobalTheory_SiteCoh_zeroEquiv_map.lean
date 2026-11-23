-- Prove2me | solution 1 for GlobalTheory.SiteCoh.zeroEquiv_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:01.156828+00:00
-- url     : https://prove2.me/submissions/19fff7b7-54ac-4970-99e4-08d390831e93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf
import Theorems.Thm_GlobalTheory_SiteCoh_freeSheafHomEquiv_comp
import Theorems.Thm_GlobalTheory_SiteCoh_extEquiv_map
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
theorem _root_.solution {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (U : C) (x : F.H' 0 U) :
    zeroEquiv G U (map f 0 U x) = f.hom.app (op U) (zeroEquiv F U x) := by
  obtain ⟨y, rfl⟩ := (extEquiv F 0 U).symm.surjective x
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  rw [zeroEquiv_mk₀, ← freeSheafHomEquiv_comp, ← zeroEquiv_mk₀]
  congr 1
  apply (extEquiv G 0 U).injective
  rw [extEquiv_map, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, Ext.mk₀_comp_mk₀]
end GlobalTheory.SiteCoh
