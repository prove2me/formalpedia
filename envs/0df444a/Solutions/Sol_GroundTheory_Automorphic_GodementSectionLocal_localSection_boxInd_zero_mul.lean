-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.localSection_boxInd_zero_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:43:30.5849+00:00
-- url     : https://prove2.me/submissions/932a5520-6f9d-431e-aa46-33ee0766536c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_modPow_units_eq_zpow
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localSection_mul
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_vecMul_mem_box_iff
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_ord_det_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_apply_eq_one_of_isUnramified
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open GroundTheory.LocalField
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution {χ₁ χ₂ : Fˣ →* ℂˣ} (hu₁ : IsUnramifiedChar χ₁) (s : ℂ)
    (g : GL (Fin 2) F) {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    localSection χ₁ χ₂ s (boxInd F 0) (g * k) = localSection χ₁ χ₂ s (boxInd F 0) g := by
  have hR : rightTranslate k (boxInd F 0) = boxInd F 0 := by
    funext x
    simp only [rightTranslate, boxInd]
    by_cases hx : x ∈ box F 0
    · have h' : x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ (box F 0 : Set (Fin 2 → F)) :=
        (vecMul_mem_box_iff hk 0 x).2 hx
      rw [Set.indicator_of_mem (show x ∈ (box F 0 : Set (Fin 2 → F)) from hx),
        Set.indicator_of_mem h']
      rfl
    · have h' : x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∉ (box F 0 : Set (Fin 2 → F)) :=
        fun h ↦ hx ((vecMul_mem_box_iff hk 0 x).1 h)
      rw [Set.indicator_of_notMem (show x ∉ (box F 0 : Set (Fin 2 → F)) from hx),
        Set.indicator_of_notMem h']
  rw [localSection_mul, hR, apply_eq_one_of_isUnramified hu₁ (ord_det_eq_zero hk),
    modPow_units_eq_zpow, ord_det_eq_zero hk]
  simp
end GroundTheory.Automorphic.GodementSectionLocal
