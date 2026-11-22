-- Prove2me | solution 1 for LongGapsBetweenPrimes.tupleAmplitude_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:56.316545+00:00
-- url     : https://prove2.me/submissions/5c6082cc-8613-432b-b973-3560e2b233d4

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ}
    (h : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) (r : DivisorTuple P k) :
    |tupleAmplitude r| ≤ 1 := by
  rw [tupleAmplitude, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
    (fun i _ => h _ (r i).property)
end LongGapsBetweenPrimes
