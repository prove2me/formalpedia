-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.mem_blkG_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:00:08.585175+00:00
-- url     : https://prove2.me/submissions/8efb4cd2-4f6a-4c74-9891-1051e3af9c75

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_unblk_blk
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_isUnit_blk_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.AdmGL.unblk_blk

set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}
namespace GlobalTheory.CompanionTheory.AdmGL
theorem _root_.solution (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ} :
    g ∈ blkG e ↔ IsUnit g ∧ blk e (unblk e g) = g := by
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact ⟨(GlobalTheory.CompanionTheory.AdmGL.isUnit_blk_iff e M).2 hM, by rw [GlobalTheory.CompanionTheory.AdmGL.unblk_blk]⟩
  · rintro ⟨hg, hg'⟩
    refine ⟨GlobalTheory.CompanionTheory.AdmGL.unblk e g, ?_, hg'⟩
    rw [← hg'] at hg
    exact (GlobalTheory.CompanionTheory.AdmGL.isUnit_blk_iff e _).1 hg
end GlobalTheory.CompanionTheory.AdmGL
