-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignmentProduct_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:36.844455+00:00
-- url     : https://prove2.me/submissions/f8838efd-fac6-4183-957d-214a26364f1b

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    0 < assignmentProduct (fun p : PrimeIndex P => p.val) σ := by
  exact Finset.prod_pos fun p _ => (Nat.prime_of_mem_primeFactors p.property).pos
end LongGapsBetweenPrimes
