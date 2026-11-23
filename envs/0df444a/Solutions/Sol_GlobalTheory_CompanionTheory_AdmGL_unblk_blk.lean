-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.unblk_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:13.217049+00:00
-- url     : https://prove2.me/submissions/70289da7-fb3a-4f9a-97d9-4612960184ee

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_apply

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
    unblk e (blk e M) = M := by
  ext p q w
  simp [unblk, blk_apply]
end GlobalTheory.CompanionTheory.AdmGL
