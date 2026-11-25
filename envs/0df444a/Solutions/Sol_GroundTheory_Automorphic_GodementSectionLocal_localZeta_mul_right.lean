-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.localZeta_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:47.834144+00:00
-- url     : https://prove2.me/submissions/622fd416-4d02-49b4-a0c4-2ae0d889dfc8

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_modPow_mul
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_modPow_add
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
theorem _root_.solution (f : F → ℂ) (μ : Fˣ →* ℂˣ) (s : ℂ) (d : Fˣ) :
    localZeta (fun t ↦ f (t * d)) μ s =
      (((μ d)⁻¹ : ℂˣ) : ℂ) * modPow (d : F) (-s) * localZeta f μ s := by
  set G : Fˣ → ℂ := fun x ↦ f x * ((μ x : ℂˣ) : ℂ) * modPow (x : F) s with hG
  have h1 : modPow (d : F) (-s) * modPow (d : F) s = 1 := by
    rw [← modPow_add d.ne_zero, neg_add_cancel]; simp [modPow]
  have h2 : (((μ d)⁻¹ : ℂˣ) : ℂ) * ((μ d : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hpt : ∀ x : Fˣ, f ((x : F) * d) * ((μ x : ℂˣ) : ℂ) * modPow (x : F) s =
      (((μ d)⁻¹ : ℂˣ) : ℂ) * modPow (d : F) (-s) * G (d * x) := by
    intro x
    simp only [hG, Units.val_mul, map_mul, modPow_mul]
    rw [mul_comm (d : F) (x : F)]
    linear_combination (-(f ((x : F) * d) * ((μ x : ℂˣ) : ℂ) * modPow (x : F) s)) *
      ((((μ d)⁻¹ : ℂˣ) : ℂ) * ((μ d : ℂˣ) : ℂ) * h1 + h2)
  have : localZeta (fun t ↦ f (t * d)) μ s =
      ∫ x, (((μ d)⁻¹ : ℂˣ) : ℂ) * modPow (d : F) (-s) * G (d * x) ∂multHaar F :=
    integral_congr_ae (Eventually.of_forall fun x ↦ hpt x)
  rw [this, integral_const_mul, integral_mul_left_eq_self G d]
  rfl
end GroundTheory.Automorphic.GodementSectionLocal
