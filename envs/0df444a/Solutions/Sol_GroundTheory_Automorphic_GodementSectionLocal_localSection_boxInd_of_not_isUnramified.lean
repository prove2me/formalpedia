-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.localSection_boxInd_of_not_isUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:43:13.333921+00:00
-- url     : https://prove2.me/submissions/4ec22c2c-5c34-4e3a-ab09-b4e5de1b0e83

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_modPow_units_eq_zpow
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localSection_smul_arg
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_smul_mem_box_iff
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_eq_zero_of_eq_mul_of_ne_one
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
theorem _root_.solution (χ₁ χ₂ : Fˣ →* ℂˣ)
    (hμ : ¬ IsUnramifiedChar (χ₁ * χ₂⁻¹)) (s : ℂ) (N : ℤ) :
    localSection χ₁ χ₂ s (boxInd F N) = 0 := by
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ unitFiltrationUnits F 0, (χ₁ * χ₂⁻¹) v ≠ 1 := by
    by_contra h
    push Not at h
    exact hμ fun v hv ↦ MonoidHom.mem_ker.2 (h v hv)
  have hord : ord (v : F) = 0 := mem_unitFiltrationUnits_zero_iff_ord.1 hv
  have hinv : (fun x ↦ boxInd F N ((v : F) • x)) = boxInd F N := by
    funext x
    have hiff : (v : F) • x ∈ box F N ↔ x ∈ box F N := by
      rw [smul_mem_box_iff, hord, sub_zero]
    by_cases hx : x ∈ box F N
    · simp [boxInd, Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]
    · simp [boxInd, Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hiff.1 hx)]
  have h := localSection_smul_arg χ₁ χ₂ s (boxInd F N) v
  rw [hinv, modPow_units_eq_zpow, hord, zpow_zero, mul_one] at h
  have hne : ((((χ₁ * χ₂⁻¹) v)⁻¹ : ℂˣ) : ℂ) ≠ 1 := by
    intro h1
    apply hv1
    have : ((χ₁ * χ₂⁻¹) v)⁻¹ = 1 := Units.ext h1
    exact inv_eq_one.1 this
  funext g
  exact eq_zero_of_eq_mul_of_ne_one hne (congrFun h g)
end GroundTheory.Automorphic.GodementSectionLocal
