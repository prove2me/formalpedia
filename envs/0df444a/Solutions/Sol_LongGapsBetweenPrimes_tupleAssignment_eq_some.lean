-- Prove2me | solution 1 for LongGapsBetweenPrimes.tupleAssignment_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:29.217491+00:00
-- url     : https://prove2.me/submissions/84ec280b-fb8b-4f23-b3b5-74aff582e282

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_prime_coordinate_unique

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    (p : PrimeIndex P) (i : Fin k) : tupleAssignment r p = some i ↔ p.val ∣ (r i).val := by
  classical
  unfold tupleAssignment
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact Classical.choose_spec h
    · exact prime_coordinate_unique (Nat.prime_of_mem_primeFactors p.property) r hpair
        (Classical.choose_spec h)
  · simp only [false_iff]
    exact fun hi => h ⟨i, hi⟩
end LongGapsBetweenPrimes
