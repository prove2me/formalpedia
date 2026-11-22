-- Prove2me | solution 1 for LongGapsBetweenPrimes.tupleProduct_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:41:31.287795+00:00
-- url     : https://prove2.me/submissions/2e0c104a-aa99-439d-92fb-9aee41702fa2

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) : tupleProduct r ∣ P := by
  exact Fintype.prod_dvd_of_isRelPrime
    (fun i j hij => Nat.coprime_iff_isRelPrime.mp (hpair i j hij))
    (fun i => Nat.dvd_of_mem_divisors (r i).property)
end LongGapsBetweenPrimes
