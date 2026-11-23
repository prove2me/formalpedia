-- Prove2me | solution 1 for GlobalTheory.StepData.blocks_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:46.276795+00:00
-- url     : https://prove2.me/submissions/7eb12ee7-6efe-4c69-8485-98544d8ba71c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_IntM_mul_maxM
import Theorems.Thm_GlobalTheory_StepData_MaxM_mul_intM
import Theorems.Thm_GlobalTheory_StepData_mem_KO
import Theorems.Thm_GlobalTheory_StepData_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_exists_mem_KOne
import Theorems.Thm_GlobalTheory_StepData_intM_fromBlocks
import Theorems.Thm_GlobalTheory_SplitWeil_Model_KOne_le_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData
theorem _root_.solution {h : GL (a ⊕ t) k} (hh : h ∈ KO k (a ⊕ t)) (hC : MaxM h.val.toBlocks₂₁) :
    MaxM (h.val.toBlocks₁₁ * (h⁻¹).val.toBlocks₁₁ - 1) ∧ MaxM (h.val.toBlocks₂₂ * (h⁻¹).val.toBlocks₂₂ - 1) ∧
      MaxM (h⁻¹).val.toBlocks₂₁ := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hh
  have e := h.mul_inv
  have e' := h.inv_mul
  rw [← fromBlocks_toBlocks h.val] at h1
  rw [← fromBlocks_toBlocks (h⁻¹).val] at h2
  rw [← fromBlocks_toBlocks h.val, ← fromBlocks_toBlocks (h⁻¹).val, fromBlocks_multiply, ← fromBlocks_one,
    fromBlocks_inj] at e e'
  obtain ⟨i1, i2, -, i4⟩ := intM_fromBlocks.1 h1
  obtain ⟨j1, j2, j3, j4⟩ := intM_fromBlocks.1 h2
  have m1 : MaxM ((h⁻¹).val.toBlocks₁₁ * h.val.toBlocks₁₁ - 1) := by
    rw [← e'.1]; simpa using (j2.mul_maxM hC).neg
  have m2 : MaxM (h.val.toBlocks₂₂ * (h⁻¹).val.toBlocks₂₂ - 1) := by
    rw [← e.2.2.2]; simpa using (hC.mul_intM j2).neg
  obtain ⟨u, hu, hu'⟩ := exists_mem_KOne m1
  have iu := (mem_KO.1 (KOne_le_KO hu)).2
  have hinv : h.val.toBlocks₁₁ * ((u⁻¹).val * (h⁻¹).val.toBlocks₁₁) = 1 := by
    rw [mul_eq_one_comm, Matrix.mul_assoc, ← hu', Units.inv_mul]
  have m3 : MaxM (h⁻¹).val.toBlocks₂₁ := by
    have : (h⁻¹).val.toBlocks₂₁ = -((h⁻¹).val.toBlocks₂₂ * h.val.toBlocks₂₁) * ((u⁻¹).val * (h⁻¹).val.toBlocks₁₁) := by
      rw [← eq_neg_of_add_eq_zero_left e'.2.2.1, Matrix.mul_assoc, hinv, Matrix.mul_one]
    rw [this]
    exact (j4.mul_maxM hC).neg.mul_intM (iu.mul j1)
  refine ⟨?_, m2, m3⟩
  rw [← e.1]; simpa using (i2.mul_maxM m3).neg
end GlobalTheory.StepData
