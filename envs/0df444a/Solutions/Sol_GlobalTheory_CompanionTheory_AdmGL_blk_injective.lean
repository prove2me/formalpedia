-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.blk_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:03:36.805187+00:00
-- url     : https://prove2.me/submissions/c3e70e82-9b7f-4546-b3da-95d58e915cf5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_unblk_blk
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
theorem _root_.solution (e : Fin a × ι ≃ Fin n) : Function.Injective (blk e) := by
  intro M N h
  rw [← GlobalTheory.CompanionTheory.AdmGL.unblk_blk e M, h, GlobalTheory.CompanionTheory.AdmGL.unblk_blk]
end GlobalTheory.CompanionTheory.AdmGL
