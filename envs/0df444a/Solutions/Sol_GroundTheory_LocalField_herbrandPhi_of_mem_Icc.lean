-- Prove2me | solution 1 for GroundTheory.LocalField.herbrandPhi_of_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:03.654784+00:00
-- url     : https://prove2.me/submissions/0d01f6fe-152c-4bf0-beff-dd47427e3a9d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Theorems.Thm_GroundTheory_LocalField_herbrandPhiOrderIso_apply
import Theorems.Thm_GroundTheory_LocalField_herbrandPhi_herbrandPsi
import Theorems.Thm_GroundTheory_LocalField_herbrandPsi_herbrandPhi
import Theorems.Thm_GroundTheory_LocalField_herbrandPsi_zero
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_trans
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_inv
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_one
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_restrictScalars
import Theorems.Thm_GroundTheory_LocalField_one_le_lowerIndex_iff
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
attribute [local simp] GroundTheory.LocalField.lowerIndex_inv
attribute [local simp] GroundTheory.LocalField.lowerIndex_one
attribute [local simp] GroundTheory.LocalField.lowerIndex_restrictScalars
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


attribute [local simp] GroundTheory.LocalField.herbrandPhiOrderIso_apply
attribute [local simp] GroundTheory.LocalField.herbrandPhi_herbrandPsi
attribute [local simp] GroundTheory.LocalField.herbrandPsi_herbrandPhi
attribute [local simp] GroundTheory.LocalField.herbrandPsi_zero

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Filter Topology MeasureTheory
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (n : ℝ) (n + 1)) :
    herbrandPhi K L u = herbrandPhi K L n +
      (u - n) / ((lowerRamificationGroup K L ((n : ℤ) + 1)).relIndex
        (lowerRamificationGroup K L 0) : ℝ) := by
  classical
  have hG : lowerRamificationGroup K L ((n : ℤ) + 1) = lowerRamificationGroupReal K L ((n : ℝ) + 1) := by
    rw [← lowerRamificationGroupReal_intCast]
    push_cast
    rfl
  have h : ∀ σ : L ≃ₐ[K] L, (if σ ∈ lowerRamificationGroup K L 0 then
      enatMin (lowerIndex K L σ - 1) u else 0) =
        (if σ ∈ lowerRamificationGroup K L 0 then enatMin (lowerIndex K L σ - 1) n else 0) +
          (u - n) * if σ ∈ lowerRamificationGroup K L 0 ∧
            σ ∈ lowerRamificationGroupReal K L ((n : ℝ) + 1) then 1 else 0 := by
    intro σ
    by_cases h0 : σ ∈ lowerRamificationGroup K L 0
    · simp only [h0, true_and, if_true]
      have h1 := one_le_lowerIndex_iff.mpr h0
      generalize hn : lowerIndex K L σ = N at h1
      induction N using ENat.recTopCoe with
      | top =>
        have : σ ∈ lowerRamificationGroupReal K L ((n : ℝ) + 1) := by
          rw [mem_lowerRamificationGroupReal_iff, hn, enatMin_top]
        simp [this]
      | coe m =>
        have hm : 1 ≤ m := by exact_mod_cast h1
        rw [mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq hn, ← ENat.natCast_one,
          ← ENat.natCast_sub, enatMin_coe, enatMin_coe, Nat.cast_sub hm, Nat.cast_one]
        by_cases hmn : (n : ℝ) + 1 + 1 ≤ m
        · rw [if_pos hmn, min_eq_right (by linarith [hu.2]), min_eq_right (by linarith)]
          ring
        · rw [if_neg hmn]
          have hmn' : (m : ℝ) - 1 ≤ n := by
            have : m < n + 2 := by exact_mod_cast (show (m : ℝ) < n + 2 by linarith)
            have : (m : ℝ) ≤ n + 1 := by exact_mod_cast (show m ≤ n + 1 by omega)
            linarith
          rw [min_eq_left hmn', min_eq_left (hmn'.trans hu.1)]
          ring
    · simp [h0]
  rw [herbrandPhi_eq_sum, herbrandPhi_eq_sum]
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hG, div_eq_mul_inv, inv_relIndex_eq_sum]
  ring
end GroundTheory.LocalField
