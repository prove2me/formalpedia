-- Prove2me | solution 1 for GlobalTheory.PrimeRecip.inv_five_log_le_sum_inv_primes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:20.195211+00:00
-- url     : https://prove2.me/submissions/887db774-f9e8-4e76-9922-f3bfec95c4e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvFiveLogLeSumInvPrimes
import Theorems.Thm_GlobalTheory_PrimeRecip_okAll_sound
import Theorems.Thm_GlobalTheory_PrimeRecip_inv_five_log_le_sum_inv_primes_of_large
import Theorems.Thm_GlobalTheory_PrimeRecip_table_ok

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
theorem _root_.solution :
    ∀ N : ℕ, 100 ≤ N → 1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by
  intro N hN
  by_cases h : N < 16900
  · exact okAll_sound table 100 16900 table_ok N hN h
  · exact inv_five_log_le_sum_inv_primes_of_large N (by omega)
end GlobalTheory.PrimeRecip
