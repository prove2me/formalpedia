-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.blk_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:26.240313+00:00
-- url     : https://prove2.me/submissions/5174c931-5f36-45cd-a772-f4a273c0fc9b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlkConjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_AdmGL_blk_apply
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
theorem _root_.solution (e : Fin a × ι ≃ Fin n) : blk e 1 = 1 := by
  ext i j
  rw [GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : e.symm i ≠ e.symm j := fun h'' => h (e.symm.injective h'')
    rw [Matrix.one_apply_ne h]
    by_cases h2 : (e.symm i).2 = (e.symm j).2
    · have h1 : (e.symm i).1 ≠ (e.symm j).1 := fun h1 => h' (Prod.ext h1 h2)
      rw [if_pos h2, Matrix.one_apply_ne h1, Pi.zero_apply]
    · rw [if_neg h2]
end GlobalTheory.CompanionTheory.AdmGL
