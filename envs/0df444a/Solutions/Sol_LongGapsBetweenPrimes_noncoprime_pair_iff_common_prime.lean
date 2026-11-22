-- Prove2me | solution 1 for LongGapsBetweenPrimes.noncoprime_pair_iff_common_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:56.719797+00:00
-- url     : https://prove2.me/submissions/5a8c2d47-7241-4d01-a2af-172024531bea

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (hP : P ≠ 0) (r : DivisorTuple P k) :
    (¬∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) ↔
      ∃ p : P.primeFactors, ∃ i j, i ≠ j ∧ p.val ∣ (r i).val ∧ p.val ∣ (r j).val := by
  classical
  simp only [not_forall, Nat.Prime.not_coprime_iff_dvd]
  constructor
  · rintro ⟨i, j, hij, p, hp, hpi, hpj⟩
    exact ⟨⟨p, hp.mem_primeFactors (hpi.trans (Nat.dvd_of_mem_divisors (r i).property)) hP⟩,
      i, j, hij, hpi, hpj⟩
  · rintro ⟨p, i, j, hij, hpi, hpj⟩
    exact ⟨i, j, hij, p, Nat.prime_of_mem_primeFactors p.property, hpi, hpj⟩
end LongGapsBetweenPrimes
