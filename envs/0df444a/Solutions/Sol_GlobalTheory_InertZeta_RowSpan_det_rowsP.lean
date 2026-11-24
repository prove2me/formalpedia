-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.det_rowsP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:27:16.968972+00:00
-- url     : https://prove2.me/submissions/b6c5a4e5-447f-42da-a0d8-25d04276c7a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasis
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowM_zero
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowM_mid
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowsP_mid
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowsP_last
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_last
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
open GlobalTheory.InertZeta Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.RowSpan
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.InertZeta.RowSpan
theorem _root_.solution {a : ℤ} {g : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {g₀ U V : Matrix (Fin N) (Fin N) L} {y : L}
    (hg10 : ∀ i, g (mid i) 0 = 0) (hg11 : ∀ i j, g (mid i) (mid j) = g₀ i j) :
    (rowsP a g U V y).det = rowsP a g U V y 0 0 * (U + V * g₀).det * y := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h1 : ∀ i : Fin (N + 1), rowsP a g U V y i.succ 0 = 0 := fun i => by
    induction i using Fin.lastCases with
    | last => rw [Fin.succ_last, rowsP_last]; simp [Matrix.one_apply]
    | cast k => exact (rowsP_mid a g U V y k).symm ▸ rowM_zero hg10 k
  simp only [h1, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul,
    Fin.succAbove_zero]
  rw [mul_assoc]
  congr 1
  rw [Matrix.det_succ_row _ (Fin.last N), Fin.sum_univ_castSucc]
  have h2 : ∀ j : Fin N, rowsP a g U V y (Fin.last N).succ j.castSucc.succ = 0 := fun j => by
    rw [Fin.succ_last, rowsP_last]; simp [Matrix.one_apply, ← mid.eq_def]; intro h; exact absurd h.symm (mid_ne_last j)
  simp only [Matrix.submatrix_apply, h2, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last]
  have h3 : ((rowsP a g U V y).submatrix Fin.succ Fin.succ).submatrix Fin.castSucc Fin.castSucc = U + V * g₀ := by
    ext i j
    simp only [Matrix.submatrix_apply]
    exact (rowsP_mid a g U V y i) ▸ rowM_mid hg11 i j
  rw [h3, Fin.succ_last, rowsP_last]
  simp [Matrix.one_apply]
  ring_nf
end GlobalTheory.InertZeta.RowSpan
