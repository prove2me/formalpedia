-- Prove2me | solution 1 for LongGapsBetweenPrimes.basisWeight_eq_tupleSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:06:33.106523+00:00
-- url     : https://prove2.me/submissions/8b4741eb-450f-42b4-a3fe-d971514332f5

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_productBasis_tupleAssignment

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (D : ℝ)
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hf : ∀ p t, f p none t = 1) (t : (p : PrimeIndex P) → Fin p.val) :
    basisWeight P k D f t =
      ∑ r ∈ tupleRegion P k D, ∏ i, coefficient P (r i).val * coordinateBasis f (r i) i t := by
  rw [basisWeight, Finset.sum_coe_sort (tupleRegion P k D)
    (fun r => tupleAmplitude r * productBasis f (tupleAssignment r) t)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [productBasis_tupleAssignment f hf r (Finset.mem_filter.mp hr).2.1 t,
    tupleAmplitude, Finset.prod_mul_distrib]
end LongGapsBetweenPrimes
