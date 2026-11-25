-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.localSection_smul_arg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:36.491567+00:00
-- url     : https://prove2.me/submissions/0478261b-1352-406f-b5e2-3b66b0fee38a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_vecMul_zero_cons
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localZeta_mul_right
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
theorem _root_.solution (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) (Φ : (Fin 2 → F) → ℂ) (a : Fˣ) :
    localSection χ₁ χ₂ s (fun x ↦ Φ ((a : F) • x)) =
      (((((χ₁ * χ₂⁻¹) a)⁻¹ : ℂˣ) : ℂ) * modPow (a : F) (-(2 * s))) • localSection χ₁ χ₂ s Φ := by
  funext g
  have hs : slice (fun x ↦ Φ ((a : F) • x)) g = fun t ↦ slice Φ g (t * a) := by
    funext t
    simp only [slice, vecMul_zero_cons]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp only [localSection, hs, localZeta_mul_right, Pi.smul_apply, smul_eq_mul]
  ring
end GroundTheory.Automorphic.GodementSectionLocal
