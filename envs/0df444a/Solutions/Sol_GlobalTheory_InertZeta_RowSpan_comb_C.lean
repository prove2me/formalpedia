-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.comb_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:57:14.709961+00:00
-- url     : https://prove2.me/submissions/bf5080fe-e8b9-4c9c-9c65-9b3b143dba3c

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
import Theorems.Thm_GlobalTheory_InertZeta_mid_injective
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_last
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_zero
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
    ∑ k, C i k • rowM g U V k = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) +
      ((C * V * g₀) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) := by
  refine vec_ext ?_ (fun j => ?_) ?_
  · rw [comb_zero hg10]; simp [Matrix.one_apply, mid_ne_zero]
  · rw [comb_mid hg11, hCM]; simp [Matrix.one_apply, mid_injective.eq_iff, mid_ne_last, last_ne_mid]
  · rw [comb_last hg12]; simp [Matrix.one_apply, mid_ne_last, Matrix.mulVec_mulVec, Matrix.mul_assoc]
end GlobalTheory.InertZeta.RowSpan
