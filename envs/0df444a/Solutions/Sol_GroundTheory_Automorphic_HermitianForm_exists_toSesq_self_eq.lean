-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.exists_toSesq_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:52:55.122903+00:00
-- url     : https://prove2.me/submissions/b0a69a37-975c-4114-b262-81cffefd94ee

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWittExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSplit
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
import Theorems.Thm_GroundTheory_Automorphic_exists_mul_norm_add_mul_norm_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_apply_self_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_isometric_prod_ofUnit
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_self_mem_range
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_left
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_right
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_mul_conj
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.coe_smul_integerUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F}
variable {E : Type*} [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]
open GroundTheory.Automorphic.HermitianForm
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution [FiniteDimensional E V] (h : HermitianForm F E V)
    (hV : 2 ≤ finrank E V) (c : Fˣ) : ∃ v, h.toSesq v v = algebraMap F E c := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := E) (by omega)
  obtain ⟨v₁, hv₁⟩ := h.exists_apply_self_ne_zero
  obtain ⟨a, ha⟩ := h.toSesq_self_mem_range v₁
  have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact hv₁ ha.symm
  obtain ⟨W, h₀, ⟨e, he⟩, hW⟩ := h.exists_isometric_prod_ofUnit (a := Units.mk0 a ha0) ha.symm
  have hW' := hW inferInstance
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := E) (by omega)
  obtain ⟨w, hw⟩ := h₀.exists_apply_self_ne_zero
  obtain ⟨b, hb⟩ := h₀.toSesq_self_mem_range w
  have hb0 : b ≠ 0 := by rintro rfl; rw [map_zero] at hb; exact hw hb.symm
  obtain ⟨x, y, hxy⟩ := exists_mul_norm_add_mul_norm_eq (E := E) (Units.mk0 a ha0)
    (Units.mk0 b hb0) c
  refine ⟨e (x, y • w), ?_⟩
  rw [he, prod_apply, ofUnit_apply, h₀.toSesq_smul_left, h₀.toSesq_smul_right, ← hb, ← hxy]
  simp only [Units.val_mk0, map_add, map_mul]
  rw [← mul_conj (F := F) x, ← mul_conj (F := F) y]
  ring
end GroundTheory.Automorphic.HermitianForm
