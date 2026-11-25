-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.det_sub_one_mem_valBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:50.901635+00:00
-- url     : https://prove2.me/submissions/2f3dbd37-7305-469a-aac4-d24170e28948

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_sub_one_mem_valBall_of_mem_congruenceSubgroup
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_mul_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
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
theorem _root_.solution {m : ℕ} {u : GL (Fin 2) F}
    (hu : u ∈ GLnLocal.congruenceSubgroup F 2 m) : (detU u : F) - 1 ∈ valBall F m := by
  have h := sub_one_mem_valBall_of_mem_congruenceSubgroup hu
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp only [Matrix.one_apply_eq, ne_eq, zero_ne_one, not_false_eq_true, Matrix.one_apply_ne,
    one_ne_zero, sub_zero] at h00 h01 h10 h11
  have hmm : valBall F ((m : ℤ) + m) ≤ valBall F m := valBall_antitone (by omega)
  have e : (detU u : F) - 1 = ((u : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) +
      ((u : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) +
      ((u : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) * ((u : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) -
      (u : Matrix (Fin 2) (Fin 2) F) 0 1 * (u : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    ring
  rw [e]
  exact sub_mem (add_mem (add_mem h00 h11) (hmm (mul_mem_valBall h00 h11)))
    (hmm (mul_mem_valBall h01 h10))
end GroundTheory.Automorphic.GodementSectionLocal
