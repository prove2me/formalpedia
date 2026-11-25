-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.vecMul_zero_cons_mem_shell_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:28.734244+00:00
-- url     : https://prove2.me/submissions/9418fd88-2bec-49f3-89d1-73cbd7ddd759

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_vecMul_zero_cons
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_box_antitone
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_smul_mem_box_iff
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_vecMul_mem_shell_iff
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_zero_one_mem_shell
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
theorem _root_.solution {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2)
    (t : Fˣ) : ![0, (t : F)] ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ shell F ↔ ord (t : F) = 0 := by
  have hr := (vecMul_mem_shell_iff hk ![0, 1]).2 zero_one_mem_shell
  have he : ![0, (t : F)] ᵥ* (k : Matrix (Fin 2) (Fin 2) F) =
      (t : F) • (![0, 1] ᵥ* (k : Matrix (Fin 2) (Fin 2) F)) := by
    rw [vecMul_zero_cons, vecMul_zero_cons]
    funext j
    simp
  rw [he]
  simp only [shell, Set.mem_sdiff, SetLike.mem_coe, smul_mem_box_iff, zero_sub]
  obtain ⟨hr0, hr1⟩ := hr
  constructor
  · rintro ⟨ha, hb⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hr1 (box_antitone (by omega) ha)
    · exact hb (box_antitone (by omega) hr0)
  · intro h0
    rw [h0]
    exact ⟨by simpa using hr0, by simpa using hr1⟩
end GroundTheory.Automorphic.GodementSectionLocal
