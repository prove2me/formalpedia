-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.slice_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:46:39.89781+00:00
-- url     : https://prove2.me/submissions/29d0618f-f76c-4282-bca8-6e8e012f4c58

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_vecMul_zero_cons
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
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) (g : GL (Fin 2) F) :
    slice Φ g ∈ schwartzBruhat F := by
  have hrow : ∃ j, (g : Matrix (Fin 2) (Fin 2) F) 1 j ≠ 0 := by
    by_contra h
    push Not at h
    have hdet := (Matrix.GeneralLinearGroup.det g).ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h 0, h 1] at hdet
    simp at hdet
  obtain ⟨j, hj⟩ := hrow
  have hcont : Continuous fun t : F ↦ ![0, t] ᵥ* (g : Matrix (Fin 2) (Fin 2) F) := by
    simp_rw [vecMul_zero_cons]
    exact continuous_pi fun i ↦ continuous_id.mul continuous_const
  have hemb : IsClosedEmbedding fun t : F ↦ ![0, t] ᵥ* (g : Matrix (Fin 2) (Fin 2) F) :=
    Function.LeftInverse.isClosedEmbedding
      (f := fun y : Fin 2 → F ↦ y j / (g : Matrix (Fin 2) (Fin 2) F) 1 j)
      (fun t ↦ by simp [vecMul_zero_cons, hj]) ((continuous_apply j).div_const _) hcont
  exact ⟨hΦ.1.comp_continuous hcont, hΦ.2.comp_isClosedEmbedding hemb⟩
end GroundTheory.Automorphic.GodementSectionLocal
