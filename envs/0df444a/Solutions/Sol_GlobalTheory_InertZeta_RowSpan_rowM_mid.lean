-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.rowM_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:04:39.101151+00:00
-- url     : https://prove2.me/submissions/31c84121-7982-4b4e-aea5-71adfd9ce851

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_injective
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
variable {g : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {g₀ U V : Matrix (Fin N) (Fin N) L} {b : Fin N → L}
namespace GlobalTheory.InertZeta.RowSpan
theorem _root_.solution (hg11 : ∀ i j, g (mid i) (mid j) = g₀ i j) (k j : Fin N) :
    rowM g U V k (mid j) = (U + V * g₀) k j := by
  simp [rowM, Finset.sum_apply, Matrix.one_apply, hg11, mid_injective.eq_iff, Matrix.mul_apply]
end GlobalTheory.InertZeta.RowSpan
