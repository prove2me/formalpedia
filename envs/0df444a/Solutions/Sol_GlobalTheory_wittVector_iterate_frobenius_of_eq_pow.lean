-- Prove2me | solution 1 for GlobalTheory.wittVector_iterate_frobenius_of_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:36.435345+00:00
-- url     : https://prove2.me/submissions/52046678-8186-4bc1-adb7-cf6337168f00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorEqTeichmullerOfFrobeniusEqPowSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory
open WittVector
namespace GlobalTheory
theorem _root_.solution {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    (y : WittVector l O) (h : frobenius y = y ^ l) (k : ℕ) :
    (WittVector.frobenius (p := l) (R := O))^[k] y = y ^ l ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_pow, h, ← pow_mul, pow_succ', mul_comm]
end GlobalTheory
