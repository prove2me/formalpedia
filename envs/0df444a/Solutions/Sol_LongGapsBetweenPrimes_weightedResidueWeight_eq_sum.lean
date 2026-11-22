-- Prove2me | solution 1 for LongGapsBetweenPrimes.weightedResidueWeight_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:41.374412+00:00
-- url     : https://prove2.me/submissions/5d88e391-4f47-4fb0-adf7-26adc756ca35

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_productBasis_tupleAssignment

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (b : DivisorTuple P k → ℝ)
    (t : (p : PrimeIndex P) → Fin p.val) :
    weightedResidueWeight P k D root b t =
      ∑ r ∈ tupleRegion P k D, b r *
        ∏ i, coefficient P (r i).val *
          coordinateBasis (fun p => rawLocalBasis (root p)) (r i) i t := by
  rw [weightedResidueWeight, Finset.sum_coe_sort (tupleRegion P k D)
    (fun r => b r * tupleAmplitude r *
      productBasis (fun p => rawLocalBasis (root p)) (tupleAssignment r) t)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [productBasis_tupleAssignment _ (fun _ _ => rfl) r (Finset.mem_filter.mp hr).2.1 t,
    tupleAmplitude, Finset.prod_mul_distrib, mul_assoc]
end LongGapsBetweenPrimes
