-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignmentPrimes_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:49.496942+00:00
-- url     : https://prove2.me/submissions/2c5f32ad-5f1c-4aff-b13c-91dca5ec2014

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_assignmentPrimes_subset

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (σ : PrimeIndex P → Option (Fin k))
    {p : ℕ} (hp : p ∈ assignmentPrimes σ) : p.Prime :=
  (Nat.mem_primeFactors.mp (assignmentPrimes_subset σ hp)).1
end LongGapsBetweenPrimes
