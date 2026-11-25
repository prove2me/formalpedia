-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.shellPiece_eq_smul_shellInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:29:32.12303+00:00
-- url     : https://prove2.me/submissions/5ca1fd5f-917a-491e-ae42-c3a551205d15

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
theorem _root_.solution {Φ : (Fin 2 → F) → ℂ} {N : ℤ}
    (hinv : ∀ x, ∀ h ∈ box F N, Φ (x + h) = Φ x) : shellPiece Φ N = Φ 0 • shellInd F := by
  funext y
  simp only [shellPiece, shellInd, Pi.smul_apply, smul_eq_mul]
  by_cases hy : y ∈ shell F
  · have hb : ((unifPow N : Fˣ) : F) • y ∈ box F N := by
      rw [smul_mem_box_iff, ord_unifPow, sub_self]
      exact hy.1
    have := hinv 0 _ hb
    rw [zero_add] at this
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Pi.one_apply, mul_one]
    exact this
  · simp [Set.indicator_of_notMem hy]
end GroundTheory.Automorphic.GodementSectionLocal
