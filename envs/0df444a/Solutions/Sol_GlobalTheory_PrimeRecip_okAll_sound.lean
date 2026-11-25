-- Prove2me | solution 1 for GlobalTheory.PrimeRecip.okAll_sound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:11:01.345263+00:00
-- url     : https://prove2.me/submissions/7de6a2e1-5e90-409d-8023-82fbdd889639

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvFiveLogLeSumInvPrimes
import Theorems.Thm_GlobalTheory_PrimeRecip_okIv_sound

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
theorem _root_.solution : ∀ (T : List (ℕ × ℕ × ℕ × ℕ × List ℕ)) (lo hi : ℕ), okAll lo T hi = true →
    ∀ N, lo ≤ N → N < hi → 1 / (5 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p
  | [], lo, hi, h, N, h1, h2 => by simp [okAll] at h; omega
  | (a, b, j, c, L) :: rest, lo, hi, h, N, h1, h2 => by
    simp only [okAll, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hal, hiv⟩, hrest⟩ := h
    by_cases hNb : N < b
    · exact okIv_sound hiv N (by omega) hNb
    · exact solution rest b hi hrest N (by omega) h2
end GlobalTheory.PrimeRecip
