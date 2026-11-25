-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.boxInd_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:15:28.794181+00:00
-- url     : https://prove2.me/submissions/a3c2289b-263f-4a09-9f8a-f93710fec966

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_smul_mem_box_iff
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_ord_unifPow
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
theorem _root_.solution (n : ℤ) :
    boxInd F (n + 1) = fun x ↦ boxInd F n (((unifPow (-1) : Fˣ) : F) • x) := by
  funext x
  have hiff : ((unifPow (-1) : Fˣ) : F) • x ∈ box F n ↔ x ∈ box F (n + 1) := by
    rw [smul_mem_box_iff, ord_unifPow, sub_neg_eq_add]
  simp only [boxInd]
  by_cases hx : x ∈ box F (n + 1)
  · have hx' : ((unifPow (-1) : Fˣ) : F) • x ∈ (box F n : Set (Fin 2 → F)) := hiff.2 hx
    rw [Set.indicator_of_mem (show x ∈ (box F (n + 1) : Set (Fin 2 → F)) from hx),
      Set.indicator_of_mem hx']
    rfl
  · have hx' : ((unifPow (-1) : Fˣ) : F) • x ∉ (box F n : Set (Fin 2 → F)) := mt hiff.1 hx
    rw [Set.indicator_of_notMem (show x ∉ (box F (n + 1) : Set (Fin 2 → F)) from hx),
      Set.indicator_of_notMem hx']
end GroundTheory.Automorphic.GodementSectionLocal
