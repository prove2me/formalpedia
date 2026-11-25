-- Prove2me | solution 1 for GroundTheory.LocalField.norm_le_one_of_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:34:32.994629+00:00
-- url     : https://prove2.me/submissions/6bc15745-b4a4-4f8f-baf9-1b8eaf74829a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_ExtensionsOfDegree
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_maximalUnramifiedExtensionGaloisEquiv_apply
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply
attribute [local simp] GroundTheory.LocalField.maximalUnramifiedExtensionGaloisEquiv_apply
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Polynomial IntermediateField ValuativeRel
open GroundTheory GroundTheory.LocalField
variable {L : Type*} [NontriviallyNormedField L]
namespace GroundTheory.LocalField
theorem _root_.solution {C : Type*} [NormedField C] [IsUltrametricDist C]
    [NormedAlgebra L C] {g : L[X]} (hg : g.Monic) (hc : ∀ i, ‖g.coeff i‖ ≤ 1) {x : C}
    (hx : aeval x g = 0) : ‖x‖ ≤ 1 := by
  by_contra h
  push Not at h
  set e := g.natDegree
  have hsum : aeval x g = x ^ e + ∑ i ∈ Finset.range e, algebraMap L C (g.coeff i) * x ^ i := by
    rw [aeval_eq_sum_range, Finset.sum_range_succ, hg.coeff_natDegree, one_smul, add_comm]
    simp only [Algebra.smul_def]
    rfl
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    linarith
  have h1 : ‖∑ i ∈ Finset.range e, algebraMap L C (g.coeff i) * x ^ i‖ < ‖x ^ e‖ := by
    rcases (Finset.range e).eq_empty_or_nonempty with he | he
    · rw [he, Finset.sum_empty, norm_zero, norm_pow]
      exact pow_pos (norm_pos_iff.2 hx0) _
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty he
        (fun i ↦ algebraMap L C (g.coeff i) * x ^ i)
      refine hle.trans_lt ?_
      rw [norm_mul, norm_algebraMap', norm_pow, norm_pow]
      calc ‖g.coeff i‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by
            gcongr
            exact hc i
        _ < ‖x‖ ^ e := by
            rw [one_mul]
            exact pow_lt_pow_right₀ h (Finset.mem_range.1 hi)
  have h2 : x ^ e = -∑ i ∈ Finset.range e, algebraMap L C (g.coeff i) * x ^ i := by
    rw [hsum] at hx
    exact eq_neg_of_add_eq_zero_left hx
  rw [h2, norm_neg] at h1
  exact lt_irrefl _ h1
end GroundTheory.LocalField
