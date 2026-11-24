-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.continuous_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:40:15.283512+00:00
-- url     : https://prove2.me/submissions/c35c0eff-f227-4330-9eb8-e392882bb023

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_apply
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
theorem _root_.solution (e : Fin a × ι ≃ Fin n) : Continuous (blk e) := by
  apply continuous_matrix
  intro i j
  simp only [GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  by_cases h : (e.symm i).2 = (e.symm j).2
  · simp only [if_pos h]
    exact (continuous_apply _).comp (continuous_id.matrix_elem _ _)
  · simp only [if_neg h]
    exact continuous_const
end GlobalTheory.CompanionTheory.AdmGL
