-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.localSection_eq_of_support_subset_shell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:39:12.841305+00:00
-- url     : https://prove2.me/submissions/3963dae7-5ac9-418f-afa2-c624eecbd9c9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_modPow_units_eq_zpow
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_vecMul_zero_cons_mem_shell_iff
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_ord_det_eq_zero
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
theorem _root_.solution (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ)
    {Ψ : (Fin 2 → F) → ℂ} (hΨ : Function.support Ψ ⊆ shell F) {k : GL (Fin 2) F}
    (hk : k ∈ GLnLocal.integralGL F 2) :
    localSection χ₁ χ₂ s Ψ k = (χ₁ (detU k) : ℂ) *
      ∫ u, slice Ψ k u * (((χ₁ * χ₂⁻¹) u : ℂˣ) : ℂ) ∂multHaar F := by
  have hdet : modPow (detU k : F) s = 1 := by
    rw [modPow_units_eq_zpow, ord_det_eq_zero hk, zpow_zero]
  simp only [localSection, hdet, mul_one, localZeta]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
  by_cases hu : slice Ψ k u = 0
  · simp [hu]
  · have hord : ord (u : F) = 0 :=
      (vecMul_zero_cons_mem_shell_iff hk u).1 (hΨ hu)
    have : ((modulus (u : F) : ℝ) : ℂ) ^ (2 * s) = 1 := by
      rw [← modPow, modPow_units_eq_zpow, hord, zpow_zero]
    simp only [this, mul_one]
end GroundTheory.Automorphic.GodementSectionLocal
