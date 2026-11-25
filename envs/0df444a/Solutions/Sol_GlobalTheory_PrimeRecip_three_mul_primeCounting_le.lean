-- Prove2me | solution 1 for GlobalTheory.PrimeRecip.three_mul_primeCounting_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:54:19.069318+00:00
-- url     : https://prove2.me/submissions/6e9f94db-8dae-41f7-8578-12ea163049f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvFiveLogLeSumInvPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
open GlobalTheory GlobalTheory.PrimeRecip
namespace GlobalTheory.PrimeRecip
theorem _root_.solution (s : ℕ) (hs : 6 ≤ s) : 3 * Nat.primeCounting s ≤ s + 9 := by
  have h := Nat.primeCounting_add_le (a := 6) (k := 6) (by norm_num) le_rfl (s - 6)
  rw [show 6 + (s - 6) = s by omega] at h
  have h6 : Nat.primeCounting 6 = 3 := by decide
  have ht : Nat.totient 6 = 2 := by decide
  rw [h6, ht] at h
  omega
end GlobalTheory.PrimeRecip
