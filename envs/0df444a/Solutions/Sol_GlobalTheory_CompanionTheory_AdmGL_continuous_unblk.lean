-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.continuous_unblk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:40:15.991275+00:00
-- url     : https://prove2.me/submissions/5306b5d2-add3-4d8d-873c-71a45322d176

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_unblk_blk
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_one
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_add
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_conjTranspose
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
theorem _root_.solution (e : Fin a × ι ≃ Fin n) : Continuous (unblk e) := by
  apply continuous_matrix
  intro p q
  apply continuous_pi
  intro w
  simp only [GlobalTheory.CompanionTheory.AdmGL.unblk, Matrix.of_apply]
  exact continuous_id.matrix_elem _ _
end GlobalTheory.CompanionTheory.AdmGL
