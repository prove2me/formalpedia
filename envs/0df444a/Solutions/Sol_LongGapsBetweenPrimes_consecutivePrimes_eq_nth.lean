-- Prove2me | solution 1 for LongGapsBetweenPrimes.consecutivePrimes_eq_nth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:13.915938+00:00
-- url     : https://prove2.me/submissions/c731df88-c4c3-4738-98c1-a6c1c7115b74

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p q : ℕ} (h : ConsecutivePrimes p q) :
    ∃ n : ℕ, Nat.nth Nat.Prime n = p ∧ Nat.nth Nat.Prime (n + 1) = q := by
  rcases h with ⟨hp, hq, hpq, hgap⟩
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hn : Nat.count Nat.Prime p < Nat.count Nat.Prime q := by
    apply hmono.lt_iff_lt.mp
    simpa only [Nat.nth_count hp, Nat.nth_count hq] using hpq
  refine ⟨Nat.count Nat.Prime p, Nat.nth_count hp, ?_⟩
  apply le_antisymm
  · simpa only [Nat.nth_count hq] using hmono.monotone (Nat.succ_le_of_lt hn)
  · by_contra! hlt
    exact hgap _
      (by simpa only [Nat.nth_count hp] using hmono (Nat.lt_succ_self (Nat.count Nat.Prime p)))
      hlt (Nat.nth_mem _ (fun hf => (Nat.infinite_setOfPred_prime hf).elim))
end LongGapsBetweenPrimes
