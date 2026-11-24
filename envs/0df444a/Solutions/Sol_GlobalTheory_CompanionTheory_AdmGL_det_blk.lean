-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.det_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:19.371891+00:00
-- url     : https://prove2.me/submissions/98a23171-51b1-4de8-a4cb-e24a2e73f6bd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}
namespace GlobalTheory.CompanionTheory.AdmGL
theorem _root_.solution (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    (blk e M).det = ∏ w, (atPlace M w).det := by
  rw [blk, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
end GlobalTheory.CompanionTheory.AdmGL
