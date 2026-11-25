-- Prove2me | solution 1 for GlobalTheory.BadShare.TwoRoots.sum_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:04:54.330431+00:00
-- url     : https://prove2.me/submissions/04cd9025-1bfb-4669-bce1-af97e9d6c723

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardIrreducibleSamePrimeToPartRootsLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.TwoRoots
namespace GlobalTheory.BadShare.TwoRoots
theorem _root_.solution {g : ℕ} (hg : 2 ≤ g) (m : ℕ) : ∑ e ∈ Finset.Icc 1 m, g ^ e ≤ 2 * g ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), pow_succ]
    nlinarith [Nat.zero_le (g ^ m)]
end GlobalTheory.BadShare.TwoRoots
