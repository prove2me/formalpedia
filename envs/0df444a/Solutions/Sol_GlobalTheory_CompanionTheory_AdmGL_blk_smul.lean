-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.blk_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:05:20.94871+00:00
-- url     : https://prove2.me/submissions/b16bfc0d-c194-414d-8d88-e4c38ba40e79

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_unblk_blk
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_one
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_add
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

set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}
namespace GlobalTheory.CompanionTheory.AdmGL
theorem _root_.solution (e : Fin a × ι ≃ Fin n) (c : ℂ) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e (c • M) = c • blk e M := by
  ext i j
  rw [Matrix.smul_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  split_ifs <;> simp
end GlobalTheory.CompanionTheory.AdmGL
