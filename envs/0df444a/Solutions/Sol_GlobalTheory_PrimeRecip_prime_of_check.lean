-- Prove2me | solution 1 for GlobalTheory.PrimeRecip.prime_of_check
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:14.430568+00:00
-- url     : https://prove2.me/submissions/6afdfdf1-65bb-4f3a-b953-ae895be09705

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvFiveLogLeSumInvPrimes
import Theorems.Thm_GlobalTheory_PrimeRecip_noSmallDiv_spec

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
theorem _root_.solution {p : ℕ} (h2 : 2 ≤ p) (hp : p < 17161) (h : noSmallDiv p 130 = true) :
    p.Prime := by
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm hms hdvd => ?_⟩
  have hmm : m * m ≤ p := Nat.le_sqrt.1 hms
  have hm130 : m ≤ 130 := by nlinarith
  exact noSmallDiv_spec p 130 h m hm hm130 hmm (Nat.dvd_iff_mod_eq_zero.1 hdvd)
end GlobalTheory.PrimeRecip
