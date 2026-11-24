-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.atPlace_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:17:25.381574+00:00
-- url     : https://prove2.me/submissions/2548916b-efb0-43db-be52-9b8e2ed505f5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_unblk_blk
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_one
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
theorem _root_.solution (M N : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) :
    atPlace (M * N) w = atPlace M w * atPlace N w := by
  ext p q
  simp [atPlace, Matrix.mul_apply, Finset.sum_apply]
end GlobalTheory.CompanionTheory.AdmGL
