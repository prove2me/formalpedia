-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.localSection_borelElt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:36:51.768965+00:00
-- url     : https://prove2.me/submissions/f8824b69-9b54-46bc-9811-d8fb73aefea2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_modPow_mul
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_modPow_add
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_det_borelElt
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localZeta_mul_right
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_slice_borelElt_mul
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
theorem _root_.solution (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) (Φ : (Fin 2 → F) → ℂ) (a d : Fˣ)
    (x : F) (g : GL (Fin 2) F) :
    localSection χ₁ χ₂ s Φ (borelElt a d x * g) =
      (χ₁ a : ℂ) * (χ₂ d : ℂ) * modPow (a : F) s * modPow (d : F) (-s) *
        localSection χ₁ χ₂ s Φ g := by
  simp only [localSection, slice_borelElt_mul, localZeta_mul_right, det_borelElt,
    map_mul, Units.val_mul, modPow_mul]
  have hμ : (((χ₁ * χ₂⁻¹) d)⁻¹ : ℂˣ) = (χ₁ d)⁻¹ * χ₂ d := by
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv]
  have h1 : modPow (d : F) s * modPow (d : F) (-(2 * s)) = modPow (d : F) (-s) := by
    rw [← modPow_add d.ne_zero]; congr 1; ring
  have h2 : ((χ₁ d : ℂˣ) : ℂ) * (((χ₁ d)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hμ, Units.val_mul, ← h1]
  linear_combination ((χ₁ a : ℂˣ) : ℂ) * ((χ₂ d : ℂˣ) : ℂ) * modPow (a : F) s *
    modPow (d : F) s * modPow (d : F) (-(2 * s)) * ((χ₁ (detU g) : ℂˣ) : ℂ) *
    modPow (detU g : F) s * localZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s) * h2
end GroundTheory.Automorphic.GodementSectionLocal
