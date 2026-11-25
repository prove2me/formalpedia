-- Prove2me | solution 1 for GlobalTheory.T.inv_five_log_le_sum_inv_primes_half_interval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:28:49.825991+00:00
-- url     : https://prove2.me/submissions/0e5f3ebd-8122-4e0c-bc22-4adf53d5cf59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvFiveLogLeSumInvPrimes
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvFiveLogLeSumInvPrimesStatement
import Theorems.Thm_GlobalTheory_PrimeRecip_inv_five_log_le_sum_inv_primes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ N : ℕ, 100 ≤ N → 1 / (5 * Real.log N) ≤ ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N), (1 : ℝ) / p := by
  first | exact @GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes | exact GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes | (intros; apply GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes <;> assumption)
end _root_.GlobalTheory.T
