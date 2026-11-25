-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.localSection_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:36:34.751549+00:00
-- url     : https://prove2.me/submissions/9b0789d6-5783-4250-9bf5-af08ba5330b5

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
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
theorem _root_.solution (χ₁ χ₂ : Fˣ →* ℂˣ) (s c : ℂ) (Φ : (Fin 2 → F) → ℂ) :
    localSection χ₁ χ₂ s (c • Φ) = c • localSection χ₁ χ₂ s Φ := by
  funext g
  have hZ : localZeta (slice (c • Φ) g) (χ₁ * χ₂⁻¹) (2 * s) =
      c * localZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s) := by
    simp only [localZeta]
    rw [← integral_const_mul]
    congr 1
    funext t
    simp only [slice, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [localSection, Pi.smul_apply, smul_eq_mul, hZ]
  ring
end GroundTheory.Automorphic.GodementSectionLocal
