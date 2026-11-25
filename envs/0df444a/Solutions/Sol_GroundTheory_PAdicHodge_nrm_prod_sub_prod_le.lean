-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_prod_sub_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:27:04.129802+00:00
-- url     : https://prove2.me/submissions/9cc77981-e5c5-4092-b15c-7a726c0e4373

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_mul
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_neg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_prod
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue


attribute [local simp] GroundTheory.PAdicHodge.nrm_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_one
attribute [local simp] GroundTheory.PAdicHodge.nrm_neg
attribute [local simp] GroundTheory.PAdicHodge.nrm_eq_zero

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ι : Type*} (s : Finset ι) (a b : ι → Ω) {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ i ∈ s, nrm K (a i) ≤ 1) (hb : ∀ i ∈ s, nrm K (b i) ≤ 1)
    (h : ∀ i ∈ s, nrm K (a i - b i) ≤ δ) :
    nrm K (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hδ
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [e]
    have h1 := ih (fun i hi ↦ ha i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hb i (Finset.mem_insert_of_mem hi)) (fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
    have h2 : ∏ i ∈ s, nrm K (b i) ≤ 1 :=
      Finset.prod_le_one (fun i _ ↦ nrm_nonneg _) (fun i hi ↦ hb i (Finset.mem_insert_of_mem hi))
    refine nrm_add_le_of_le ?_ ?_
    · rw [nrm_mul]
      calc nrm K (a j) * nrm K (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ 1 * δ :=
            mul_le_mul (ha j (Finset.mem_insert_self _ _)) h1 (nrm_nonneg _) zero_le_one
        _ = δ := one_mul δ
    · rw [nrm_mul, nrm_prod]
      calc nrm K (a j - b j) * ∏ i ∈ s, nrm K (b i) ≤ δ * 1 :=
            mul_le_mul (h j (Finset.mem_insert_self _ _)) h2
              (Finset.prod_nonneg fun i _ ↦ nrm_nonneg _) hδ
        _ = δ := mul_one δ
end GroundTheory.PAdicHodge
