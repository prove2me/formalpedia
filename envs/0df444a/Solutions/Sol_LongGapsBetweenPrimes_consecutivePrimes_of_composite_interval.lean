-- Prove2me | solution 1 for LongGapsBetweenPrimes.consecutivePrimes_of_composite_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:50.522864+00:00
-- url     : https://prove2.me/submissions/0380ce3d-903e-4414-9c7b-180fcc4ac55d

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {N H : ℕ} (hN : 2 ≤ N)
    (hcomposite : ∀ n : ℕ, N < n → n ≤ N + H → ¬n.Prime) :
    ∃ p q : ℕ, ConsecutivePrimes p q ∧ p ≤ N ∧ N + H < q ∧ q ≤ 2 * N ∧ H < q - p := by
  have hex := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  let q := Nat.find hex
  obtain ⟨hq, hNq, hqN⟩ : q.Prime ∧ N < q ∧ q ≤ 2 * N := Nat.find_spec hex
  let p := Nat.findGreatest Nat.Prime N
  have hp : p.Prime := Nat.findGreatest_spec hN Nat.prime_two
  have hpN : p ≤ N := Nat.findGreatest_le N
  have hNHq : N + H < q := by
    by_contra! h
    exact hcomposite q hNq h hq
  refine ⟨p, q, ⟨hp, hq, hpN.trans_lt hNq, ?_⟩, hpN, hNHq, hqN, by omega⟩
  intro r hpr hrq hr
  by_cases hrN : r ≤ N
  · exact Nat.findGreatest_is_greatest hpr hrN hr
  · exact Nat.find_min hex hrq ⟨hr, by omega, by omega⟩
end LongGapsBetweenPrimes
