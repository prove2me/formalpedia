-- Prove2me | solution 1 for GlobalTheory.ClassMin.exists_basis_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:12:12.3899+00:00
-- url     : https://prove2.me/submissions/58a6c451-34eb-4d66-a305-088238cc1c24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsShiftedLtClassMin
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Module
open scoped Pointwise
variable {X : Type*} [AddCommGroup X]
variable {Q : QuadraticMap ℤ X ℝ} {N : ℤ}
namespace GlobalTheory.ClassMin
theorem _root_.solution {ι : Type*} (e : Basis ι ℤ X) {ν : X →+ ℝ} (hν : ν ≠ 0) :
    ∃ i, ν (e i) < 0 ∨ ν (-e i) < 0 := by
  by_contra h
  push Not at h
  refine hν (AddMonoidHom.toIntLinearMap_injective (e.ext fun i => ?_))
  have h2 := (h i).2
  rw [map_neg] at h2
  simpa using le_antisymm (by linarith) (h i).1
end GlobalTheory.ClassMin
