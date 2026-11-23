-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.blk_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:04.419253+00:00
-- url     : https://prove2.me/submissions/7fc348de-d426-4896-8553-a15f016d79e5

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
theorem _root_.solution (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) (i j : Fin n) :
    blk e M i j = if (e.symm i).2 = (e.symm j).2 then M (e.symm i).1 (e.symm j).1 (e.symm i).2 else 0 := by
  rw [GlobalTheory.CompanionTheory.AdmGL.blk, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.blockDiagonal_apply,
    GlobalTheory.CompanionTheory.AdmGL.atPlace, Matrix.map_apply]
end GlobalTheory.CompanionTheory.AdmGL
