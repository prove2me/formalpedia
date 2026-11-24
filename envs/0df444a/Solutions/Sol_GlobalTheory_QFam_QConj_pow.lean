-- Prove2me | solution 1 for GlobalTheory.QFam.QConj.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:20:39.999951+00:00
-- url     : https://prove2.me/submissions/2efd0f7e-e0e7-458e-9593-5a18158d9e63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionsCoeffwiseConjugateRingClosure
import Theorems.Thm_GlobalTheory_QFam_QConj_const
import Theorems.Thm_GlobalTheory_QFam_QConj_mul
import Theorems.Thm_GlobalTheory_QFam_HasQ_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam
variable {g : ℂ ≃+* ℂ} {N : ℕ}
namespace GlobalTheory.QFam
namespace QConj
theorem _root_.solution (hN : 0 < N) {f f' : ℍ → ℂ} (k : ℕ) (hf : QConj g N f f') :
    QConj g N (fun τ => f τ ^ k) fun τ => f' τ ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    simpa using QConj.const g N 1
  | succ k ih =>
    simp only [pow_succ]
    exact QConj.mul hN ih hf
end QConj
end GlobalTheory.QFam
