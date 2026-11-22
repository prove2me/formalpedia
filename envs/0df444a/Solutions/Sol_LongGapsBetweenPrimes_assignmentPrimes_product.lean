-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignmentPrimes_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:42:40.946402+00:00
-- url     : https://prove2.me/submissions/4bde0834-ff61-4b57-a215-8661f0b1232e

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    (∏ p ∈ assignmentPrimes σ, p) = assignmentProduct (fun p : PrimeIndex P => p.val) σ := by
  classical
  exact Finset.prod_image Subtype.val_injective.injOn
end LongGapsBetweenPrimes
