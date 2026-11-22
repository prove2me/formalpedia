-- Prove2me | solution 1 for LongGapsBetweenPrimes.tupleAssignment_isSome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:03.429615+00:00
-- url     : https://prove2.me/submissions/93a08300-6186-43cf-b6f6-5599be3ab5c0

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (r : DivisorTuple P k) (p : PrimeIndex P) :
    (tupleAssignment r p).isSome ↔ p.val ∣ tupleProduct r := by
  classical
  simp [tupleAssignment, tupleProduct,
    (Nat.prime_of_mem_primeFactors p.property).prime.dvd_finsetProd_iff]
end LongGapsBetweenPrimes
