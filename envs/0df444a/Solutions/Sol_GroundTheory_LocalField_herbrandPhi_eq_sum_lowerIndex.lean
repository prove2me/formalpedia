-- Prove2me | solution 1 for GroundTheory.LocalField.herbrandPhi_eq_sum_lowerIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:47:23.110689+00:00
-- url     : https://prove2.me/submissions/0ec840c1-ce79-4a54-9817-fe1de2bbf4bf

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_eq_zero_iff
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
theorem _root_.solution {u : ℝ} (hu : -1 ≤ u) :
    herbrandPhi K L u = (Nat.card (lowerRamificationGroup K L 0) : ℝ)⁻¹ *
      ∑ σ : L ≃ₐ[K] L, enatMin (lowerIndex K L σ) (u + 1) - 1 := by
  classical
  have h : ∀ σ : L ≃ₐ[K] L, enatMin (lowerIndex K L σ) (u + 1) =
      (if σ ∈ lowerRamificationGroup K L 0 then enatMin (lowerIndex K L σ - 1) u else 0) +
        if σ ∈ lowerRamificationGroup K L 0 then 1 else 0 := by
    intro σ
    by_cases h0 : σ ∈ lowerRamificationGroup K L 0
    · simp only [h0, if_true]
      have h1 := one_le_lowerIndex_iff.mpr h0
      generalize lowerIndex K L σ = n at h1
      induction n using ENat.recTopCoe with
      | top => simp
      | coe m =>
        have hm : 1 ≤ m := by exact_mod_cast h1
        rw [← ENat.natCast_one, ← ENat.natCast_sub, enatMin_coe, enatMin_coe, Nat.cast_sub hm,
          Nat.cast_one, ← min_add_add_right, sub_add_cancel]
    · simp only [h0, if_false, add_zero, lowerIndex_eq_zero_iff.mpr h0]
      rw [show ((0 : ℕ∞)) = ((0 : ℕ) : ℕ∞) from rfl, enatMin_coe, Nat.cast_zero]
      exact min_eq_left (by linarith)
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_boole, card_filter_mem, herbrandPhi_eq_sum, mul_add,
    inv_mul_cancel₀ card_lowerRamificationGroup_zero_pos.ne', add_sub_cancel_right]
end GroundTheory.LocalField
