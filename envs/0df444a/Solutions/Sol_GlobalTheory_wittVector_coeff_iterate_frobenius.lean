-- Prove2me | solution 1 for GlobalTheory.wittVector_coeff_iterate_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:34.732852+00:00
-- url     : https://prove2.me/submissions/2920854f-e69e-4468-959a-ccfe184aa68f

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
    [CharP O l] (y : WittVector l O) (k n : ℕ) :
    ((WittVector.frobenius (p := l) (R := O))^[k] y).coeff n = y.coeff n ^ l ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', WittVector.coeff_frobenius_charP, ih, ← pow_mul, ← pow_succ]
end GlobalTheory
