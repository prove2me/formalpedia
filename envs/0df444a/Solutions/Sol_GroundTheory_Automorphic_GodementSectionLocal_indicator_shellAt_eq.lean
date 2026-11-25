-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.indicator_shellAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:46.570836+00:00
-- url     : https://prove2.me/submissions/6623ffc3-7209-410b-982d-ea386bd802a6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_shellAt_zero
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_smul_mem_shellAt_iff
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_unifPow_smul_unifPow_smul
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
omit [MeasurableSpace F] [BorelSpace F]
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution (Φ : (Fin 2 → F) → ℂ) (m : ℤ) :
    (shellAt F m).indicator Φ = fun x ↦ shellPiece Φ m (((unifPow (-m) : Fˣ) : F) • x) := by
  funext x
  simp only [shellPiece]
  rw [← shellAt_zero]
  by_cases hx : x ∈ shellAt F m
  · have hx' : ((unifPow (-m) : Fˣ) : F) • x ∈ shellAt F 0 := by
      rw [smul_mem_shellAt_iff]; simpa using hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', unifPow_smul_unifPow_smul]
  · have hx' : ((unifPow (-m) : Fˣ) : F) • x ∉ shellAt F 0 := by
      rw [smul_mem_shellAt_iff]; simpa using hx
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
end GroundTheory.Automorphic.GodementSectionLocal
