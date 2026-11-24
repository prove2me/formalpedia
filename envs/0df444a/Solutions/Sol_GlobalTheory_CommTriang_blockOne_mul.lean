-- Prove2me | solution 1 for GlobalTheory.CommTriang.blockOne_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:16:04.776244+00:00
-- url     : https://prove2.me/submissions/bbc7cf28-c96c-4b57-92a3-dec415337fe6

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
theorem _root_.solution (Q R : Matrix (Fin n) (Fin n) k) : blockOne Q * blockOne R = blockOne (Q * R) := by
  ext a b
  cases a using Fin.cases <;> cases b using Fin.cases <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
end GlobalTheory.CommTriang
