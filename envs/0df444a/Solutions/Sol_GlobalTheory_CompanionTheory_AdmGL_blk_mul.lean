-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.blk_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:33:16.878831+00:00
-- url     : https://prove2.me/submissions/08bcc5e5-b6ee-4bb1-8659-e86105c6facc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_unblk_blk
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_one
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_atPlace_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.AdmGL.unblk_blk
attribute [local simp] GlobalTheory.CompanionTheory.AdmGL.blk_one

set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}
namespace GlobalTheory.CompanionTheory.AdmGL
theorem _root_.solution (e : Fin a × ι ≃ Fin n) (M N : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e (M * N) = blk e M * blk e N := by
  have h : GlobalTheory.CompanionTheory.AdmGL.atPlace (M * N) = fun w => GlobalTheory.CompanionTheory.AdmGL.atPlace M w * GlobalTheory.CompanionTheory.AdmGL.atPlace N w :=
    funext (GlobalTheory.CompanionTheory.AdmGL.atPlace_mul M N)
  simp only [GlobalTheory.CompanionTheory.AdmGL.blk, Matrix.reindex_apply]
  rw [h, Matrix.blockDiagonal_mul]
  exact (Matrix.submatrix_mul_equiv _ _ _ e.symm _).symm
end GlobalTheory.CompanionTheory.AdmGL
