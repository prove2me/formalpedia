-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignmentProduct_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:54.168802+00:00
-- url     : https://prove2.me/submissions/3d036208-5674-4190-9b47-9293ca2fd5b0

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_assignmentPrimes_subset
import Theorems.Thm_LongGapsBetweenPrimes_assignmentPrimes_product

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    assignmentProduct (fun p : PrimeIndex P => p.val) σ ∣ P := by
  rw [← assignmentPrimes_product]
  exact (Finset.prod_dvd_prod_of_subset _ _ _ (assignmentPrimes_subset σ)).trans
    (Nat.prod_primeFactors_dvd P)
end LongGapsBetweenPrimes
