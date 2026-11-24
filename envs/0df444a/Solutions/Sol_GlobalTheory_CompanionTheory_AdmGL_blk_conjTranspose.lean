-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.blk_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:24:14.176191+00:00
-- url     : https://prove2.me/submissions/daffd6b9-45d9-44c9-b365-38c4b5f17e4b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_unblk_blk
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_one
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_add
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.AdmGL.unblk_blk
attribute [local simp] GlobalTheory.CompanionTheory.AdmGL.blk_one
attribute [local simp] GlobalTheory.CompanionTheory.AdmGL.blk_mul
attribute [local simp] GlobalTheory.CompanionTheory.AdmGL.blk_add
attribute [local simp] GlobalTheory.CompanionTheory.AdmGL.blk_smul

set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}
namespace GlobalTheory.CompanionTheory.AdmGL
theorem _root_.solution (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e Mᴴ = (blk e M)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  by_cases h : (e.symm i).2 = (e.symm j).2
  · rw [if_pos h, if_pos h.symm, Matrix.conjTranspose_apply, Pi.star_apply, h]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]
end GlobalTheory.CompanionTheory.AdmGL
