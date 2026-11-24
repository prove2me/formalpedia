-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.rho_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:39:59.275827+00:00
-- url     : https://prove2.me/submissions/58df7983-5a08-411f-b428-37b388bd3cff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasis
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowM_zero
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowM_mid
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowM_last
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowsP_mid
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowsP_last
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_vecOf_zero
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_vecOf_mid
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_vecOf_last
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_vec_ext
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_last_ne_mid
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_sum_idx
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


attribute [local simp] GlobalTheory.InertZeta.RowSpan.vecOf_zero
attribute [local simp] GlobalTheory.InertZeta.RowSpan.vecOf_mid
attribute [local simp] GlobalTheory.InertZeta.RowSpan.vecOf_last

set_option autoImplicit false
open GlobalTheory.InertZeta Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.RowSpan
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.InertZeta.RowSpan
theorem _root_.solution {a : ℤ} {g : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {g₀ U V C : Matrix (Fin N) (Fin N) L} {b r : Fin N → L}
    {c y z : L} (hg10 : ∀ i, g (mid i) 0 = 0) (hg11 : ∀ i j, g (mid i) (mid j) = g₀ i j)
    (hg12 : ∀ i, g (mid i) (Fin.last (N + 1)) = (g₀ *ᵥ b) i) (hCM : C * (U + V * g₀) = 1) (hy : y ≠ 0) :
    vecOf 0 (fun j => z * (r ᵥ* C) j) (z * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y) ᵥ* rowsP a g U V y =
      vecOf 0 (fun j => z * r j) (z * c) := by
  have h1 : (r ᵥ* C) ᵥ* (U + V * g₀) = r := by rw [Matrix.vecMul_vecMul, hCM, Matrix.vecMul_one]
  have h2 : (r ᵥ* C) ⬝ᵥ (V *ᵥ (g₀ *ᵥ b)) = r ⬝ᵥ ((C * V * g₀) *ᵥ b) := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine vec_ext ?_ (fun j => ?_) ?_
  · simp only [Matrix.vecMul, dotProduct, sum_idx, vecOf_zero, vecOf_mid, vecOf_last, rowsP_mid, rowsP_last,
      rowM_zero hg10]
    simp [Matrix.one_apply]
  · simp only [Matrix.vecMul, dotProduct, sum_idx, vecOf_zero, vecOf_mid, vecOf_last, rowsP_mid, rowsP_last,
      rowM_mid hg11]
    have := congrFun h1 j
    simp only [Matrix.vecMul, dotProduct] at this
    simp only [Pi.smul_apply, Matrix.one_apply, last_ne_mid, if_false, smul_eq_mul, mul_zero, add_zero, zero_mul,
      zero_add]
    rw [← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [Matrix.vecMul, dotProduct, sum_idx, vecOf_zero, vecOf_mid, vecOf_last, rowsP_mid, rowsP_last,
      rowM_last hg12]
    simp only [dotProduct] at h2
    simp only [Pi.smul_apply, Matrix.one_apply, if_true, smul_eq_mul, mul_one, zero_mul, zero_add]
    have e3 : ∀ u : Fin N → L, ∑ x, (z * ∑ x_1, r x_1 * C x_1 x) * u x = z * ∑ i, (r ᵥ* C) i * u i := fun u => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by simp only [Matrix.vecMul, dotProduct]; ring
    rw [e3, h2]
    field_simp
    ring
end GlobalTheory.InertZeta.RowSpan
