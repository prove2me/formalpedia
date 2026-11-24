-- Prove2me | solution 1 for GlobalTheory.InertZeta.hasLen_diagonal_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:28:23.032335+00:00
-- url     : https://prove2.me/submissions/8e9bd47e-1af2-4494-9452-b904743ce2f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixLengthExistsOfElementaryDivisors
import Theorems.Thm_GlobalTheory_InertZeta_prod_exp_eq
import Theorems.Thm_GlobalTheory_InertZeta_isInt_diagonal
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
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
open GlobalTheory.InertZeta
noncomputable section
open Matrix Formalism.UG
open GlobalTheory GlobalTheory.InertZeta
namespace GlobalTheory.InertZeta
theorem _root_.solution {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L}
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (d : Fin n → ℤ) :
    HasLen (Matrix.diagonal (fun i => ϖ ^ d i)) (∑ i, (-d i).toNat) := by
  have h0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hpow : ∀ m : ℕ, ϖ ^ m ∈ intL L := fun m => by
    show Valued.v (ϖ ^ m) ≤ 1
    rw [map_pow, hϖ]
    exact pow_le_one' (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num) m
  refine ⟨Matrix.diagonal (fun i => if 0 ≤ d i then 1 else 0), Matrix.diagonal (fun i => if 0 ≤ d i then 0 else 1),
    Matrix.diagonal (fun i => ϖ ^ (-d i).toNat), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact isInt_diagonal fun i => by split_ifs <;> first | exact one_mem _ | exact zero_mem _
  · exact isInt_diagonal fun i => by split_ifs <;> first | exact one_mem _ | exact zero_mem _
  · exact isInt_diagonal fun i => hpow _
  · rw [Matrix.diagonal_mul_diagonal]
    refine isInt_diagonal fun i => ?_
    have : ϖ ^ d i * ϖ ^ (-d i).toNat = ϖ ^ (d i).toNat := by
      rw [← zpow_natCast, ← zpow_add₀ h0, ← zpow_natCast]
      congr 1
      omega
    rw [this]; exact hpow _
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : 0 ≤ d i
    · simp [h, Int.toNat_eq_zero.2 (by omega : -d i ≤ 0)]
    · simp only [h, if_false, zero_mul, zero_add, one_mul]
      rw [← zpow_natCast, ← zpow_add₀ h0]
      rw [show d i + (((-d i).toNat : ℕ) : ℤ) = 0 by omega, zpow_zero]
  · rw [Matrix.det_diagonal, map_prod]
    simp only [map_pow, hϖ]
    rw [Finset.prod_congr rfl (fun i _ => (WithZero.exp_nsmul _ _).symm), prod_exp_eq]
    congr 1
    push_cast
    simp
end GlobalTheory.InertZeta
