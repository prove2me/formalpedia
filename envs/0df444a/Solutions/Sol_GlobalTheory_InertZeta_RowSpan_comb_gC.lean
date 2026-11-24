-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.comb_gC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:57:15.280748+00:00
-- url     : https://prove2.me/submissions/29ca3992-1fbb-4024-9e7a-08482f17f5ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasis
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_comb_zero
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_comb_mid
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_comb_last
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


attribute [local simp] GlobalTheory.InertZeta.RowSpan.vecOf_zero
attribute [local simp] GlobalTheory.InertZeta.RowSpan.vecOf_mid
attribute [local simp] GlobalTheory.InertZeta.RowSpan.vecOf_last

set_option autoImplicit false
open GlobalTheory.InertZeta Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.RowSpan
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
variable {g : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {g₀ U V C : Matrix (Fin N) (Fin N) L} {b : Fin N → L}
namespace GlobalTheory.InertZeta.RowSpan
theorem _root_.solution (hg10 : ∀ i, g (mid i) 0 = 0) (hg11 : ∀ i j, g (mid i) (mid j) = g₀ i j)
    (hg12 : ∀ i, g (mid i) (Fin.last (N + 1)) = (g₀ *ᵥ b) i) (hCM : C * (U + V * g₀) = 1) (i : Fin N) :
    ∑ k, (g₀ * C) i k • rowM g U V k = g (mid i) -
      ((g₀ * C * U) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) := by
  have hCU : g₀ * C * U = g₀ - g₀ * C * V * g₀ := by
    rw [eq_sub_iff_add_eq, Matrix.mul_assoc g₀ C U, Matrix.mul_assoc (g₀ * C) V, Matrix.mul_assoc g₀ C, ← Matrix.mul_add,
      ← Matrix.mul_add, hCM, Matrix.mul_one]
  refine vec_ext ?_ (fun j => ?_) ?_
  · rw [comb_zero hg10]; simp [Matrix.one_apply, hg10]
  · rw [comb_mid hg11, Matrix.mul_assoc, hCM]; simp [Matrix.one_apply, mid_ne_last, last_ne_mid, hg11]
  · rw [comb_last hg12, Pi.sub_apply, hg12, hCU, Matrix.sub_mulVec]
    simp [Matrix.one_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]
end GlobalTheory.InertZeta.RowSpan
