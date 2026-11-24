-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.isUnit_blk_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:22.404299+00:00
-- url     : https://prove2.me/submissions/41fd42ec-8c7f-46db-8e54-fe598d006405

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_unblk_blk
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_one
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_add
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_conjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_det_apply_place
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_det_blk
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
attribute [local simp] GlobalTheory.CompanionTheory.AdmGL.blk_conjTranspose

set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}
namespace GlobalTheory.CompanionTheory.AdmGL
theorem _root_.solution (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    IsUnit (blk e M) ↔ IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, GlobalTheory.CompanionTheory.AdmGL.det_blk, Pi.isUnit_iff]
  simp [isUnit_iff_ne_zero, GlobalTheory.CompanionTheory.AdmGL.det_apply_place, Finset.prod_ne_zero_iff]
end GlobalTheory.CompanionTheory.AdmGL
