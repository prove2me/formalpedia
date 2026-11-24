-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertSpan.det_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:21:21.480593+00:00
-- url     : https://prove2.me/submissions/607d6355-0eeb-4f21-9209-41217c415a35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEquality
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_first
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_middle
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_last
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_first
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_middle
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_last
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


attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_first
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_middle
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_last
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_first
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_middle
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_last

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertSpan
variable {L : Type} [Field L] {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertSpan
theorem _root_.solution (A : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (B : Matrix (Fin N) (Fin N) L)
    (h0 : ∀ i, i ≠ 0 → A i 0 = 0) (hl : ∀ j, j ≠ Fin.last (N + 1) → A (Fin.last (N + 1)) j = 0)
    (hm : ∀ i j, A (mid i) (mid j) = B i j) :
    A.det = A 0 0 * A (Fin.last (N + 1)) (Fin.last (N + 1)) * B.det := by
  have e : (A.submatrix Fin.succ Fin.succ).det = A (Fin.last (N + 1)) (Fin.last (N + 1)) * B.det := by
    rw [Matrix.det_succ_row _ (Fin.last N), Finset.sum_eq_single (Fin.last N)]
    · have : ((A.submatrix Fin.succ Fin.succ).submatrix (Fin.last N).succAbove (Fin.last N).succAbove) = B := by
        ext i j
        simpa [mid] using hm i j
      rw [this]
      simp [← two_mul, Fin.succ_last]
    · intro j _ hj
      have : j.succ ≠ Fin.last (N + 1) := fun h => hj (by simpa [← Fin.succ_last] using h)
      have h2 : A.submatrix Fin.succ Fin.succ (Fin.last N) j = 0 := by
        rw [Matrix.submatrix_apply, Fin.succ_last]
        exact hl _ this
      rw [h2]
      simp
    · simp
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0 (fun i _ hi => by rw [h0 i hi]; simp) (by simp)]
  simp only [Fin.succAbove_zero, e]
  simp [mul_assoc]
end GlobalTheory.CompanionTheory.InertSpan
