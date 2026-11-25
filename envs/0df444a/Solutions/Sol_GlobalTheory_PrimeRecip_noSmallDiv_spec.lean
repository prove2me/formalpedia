-- Prove2me | solution 1 for GlobalTheory.PrimeRecip.noSmallDiv_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:00:53.756674+00:00
-- url     : https://prove2.me/submissions/b4068dad-4b9b-4775-acdc-b8056fffebff

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
theorem _root_.solution (p : ℕ) : ∀ D, noSmallDiv p D = true →
    ∀ d, 2 ≤ d → d ≤ D → d * d ≤ p → p % d ≠ 0 := by
  intro D
  induction D with
  | zero => intro _ d h2 hD; omega
  | succ D ih =>
    intro h d h2 hD hdd
    simp only [noSmallDiv, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge d (D + 1) with hlt | hge
    · exact ih h.2 d h2 (by omega) hdd
    · have hd : d = D + 1 := by omega
      subst hd
      have h1 := h.1
      simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h1
      rcases h1 with (h1 | h1) | h1
      · omega
      · omega
      · exact h1
end GlobalTheory.PrimeRecip
