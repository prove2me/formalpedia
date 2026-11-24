-- Prove2me | solution 1 for GlobalTheory.CommTriang.conj_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:16:06.601405+00:00
-- url     : https://prove2.me/submissions/bb470bf3-262c-4b9d-add6-94c01b6ec951

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBisFurther
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonEigenvectorCommuting
import Theorems.Thm_GlobalTheory_CommTriang_blockOne_zero_zero
import Theorems.Thm_GlobalTheory_CommTriang_blockOne_zero_succ
import Theorems.Thm_GlobalTheory_CommTriang_blockOne_succ_zero
import Theorems.Thm_GlobalTheory_CommTriang_blockOne_succ_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CommTriang.blockOne_zero_zero
attribute [local simp] GlobalTheory.CommTriang.blockOne_zero_succ
attribute [local simp] GlobalTheory.CommTriang.blockOne_succ_zero
attribute [local simp] GlobalTheory.CommTriang.blockOne_succ_succ

set_option autoImplicit false
open scoped BigOperators
open GlobalTheory GlobalTheory.CommTriang
open Matrix
variable {k : Type} [Field k] {n : ℕ}
namespace GlobalTheory.CommTriang
theorem _root_.solution (R Q : Matrix (Fin n) (Fin n) k) (S : Matrix (Fin (n+1)) (Fin (n+1)) k) (a b : Fin n) :
    (blockOne R * S * blockOne Q) a.succ b.succ = (R * S.submatrix Fin.succ Fin.succ * Q) a b := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]
end GlobalTheory.CommTriang
