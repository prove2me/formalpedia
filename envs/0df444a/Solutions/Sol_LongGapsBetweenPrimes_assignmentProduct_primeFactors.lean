-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignmentProduct_primeFactors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:05.761052+00:00
-- url     : https://prove2.me/submissions/0d53fa53-f23a-4d5c-a3a5-9c7cdabfe83d

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_assignmentPrimes_prime
import Theorems.Thm_LongGapsBetweenPrimes_assignmentPrimes_product

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    (assignmentProduct (fun p : PrimeIndex P => p.val) σ).primeFactors = assignmentPrimes σ := by
  rw [← assignmentPrimes_product]
  exact Nat.primeFactors_prod (fun p hp => assignmentPrimes_prime σ hp)
end LongGapsBetweenPrimes
