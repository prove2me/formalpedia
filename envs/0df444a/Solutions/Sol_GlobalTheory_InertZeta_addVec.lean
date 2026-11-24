-- Prove2me | solution 1 for GlobalTheory.InertZeta.addVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:07:09.790896+00:00
-- url     : https://prove2.me/submissions/2a2fd4f2-0796-427b-9b83-0f9963584c00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeAddVectorDetValuation
import Theorems.Thm_GlobalTheory_InertZeta_smul_mem_integral_submodule_of_valuation_le_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_mem_rowLat
import Theorems.Thm_GlobalTheory_InertZeta_rowLat_le
import Theorems.Thm_GlobalTheory_InertZeta_row_mem_rowLat
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.InertZeta
namespace GlobalTheory.InertZeta
theorem _root_.solution : AddVec := by
  intro L _ _ n M k ρ e hM hρ he
  rcases he with rfl | ⟨i₀, hi₀⟩
  · refine ⟨M, by simpa using hM, ?_⟩
    refine sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_rowLat.2 ⟨ρ, fun i => ?_, rfl⟩))
    exact (by simpa using hρ i : Valued.v (ρ i) ≤ 1)
  · have h0 : ρ i₀ ≠ 0 := fun h => by rw [h, map_zero] at hi₀; exact WithZero.exp_ne_zero hi₀.symm
    refine ⟨M.updateRow i₀ (ρ ᵥ* M), ?_, ?_⟩
    · rw [Matrix.vecMul_eq_sum, Matrix.det_updateRow_sum, smul_eq_mul, map_mul, hi₀, hM, ← WithZero.exp_add, add_comm]
    · apply le_antisymm
      · refine sup_le (rowLat_le.2 fun i => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
        · by_cases hi : i = i₀
          · subst hi
            have hs : ρ ᵥ* M = ρ i • M i + ∑ j ∈ Finset.univ.erase i, ρ j • M j := by
              rw [Matrix.vecMul_eq_sum]; exact (Finset.add_sum_erase _ (fun j => ρ j • M j) (Finset.mem_univ _)).symm
            have : M i = (ρ i)⁻¹ • (M.updateRow i (ρ ᵥ* M)) i -
                ∑ j ∈ Finset.univ.erase i, ((ρ i)⁻¹ * ρ j) • (M.updateRow i (ρ ᵥ* M)) j := by
              rw [Matrix.updateRow_self, hs, smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul, Finset.smul_sum]
              rw [add_sub_assoc, ← Finset.sum_sub_distrib]
              rw [Finset.sum_eq_zero, add_zero]
              intro j hj
              rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hj), smul_smul, sub_self]
            rw [this]
            have hv : Valued.v (ρ i)⁻¹ = WithZero.exp (-(e : ℤ)) := by rw [map_inv₀, hi₀, WithZero.exp_neg]
            refine Submodule.sub_mem _ (smul_mem_integral_submodule_of_valuation_le_one ?_ (row_mem_rowLat _ _)) (Submodule.sum_mem _ fun j _ => smul_mem_integral_submodule_of_valuation_le_one ?_ (row_mem_rowLat _ _))
            · rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
            · rw [map_mul, hv]
              calc WithZero.exp (-(e : ℤ)) * Valued.v (ρ j) ≤ WithZero.exp (-(e : ℤ)) * WithZero.exp (e : ℤ) :=
                    mul_le_mul' le_rfl (hρ j)
                _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
          · have := row_mem_rowLat (M.updateRow i₀ (ρ ᵥ* M)) i
            rwa [Matrix.updateRow_ne hi] at this
        · have := row_mem_rowLat (M.updateRow i₀ (ρ ᵥ* M)) i₀
          rwa [Matrix.updateRow_self] at this
      · refine rowLat_le.2 fun i => ?_
        by_cases hi : i = i₀
        · subst hi
          rw [Matrix.updateRow_self]
          exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
        · rw [Matrix.updateRow_ne hi]
          exact Submodule.mem_sup_left (row_mem_rowLat _ _)
end GlobalTheory.InertZeta
