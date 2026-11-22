-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignmentVariance_tuple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:26.562792+00:00
-- url     : https://prove2.me/submissions/16809bfe-25bb-4a62-b5fc-d825e74bb8e8

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_tupleAssignment_prod
import Theorems.Thm_LongGapsBetweenPrimes_prod_primeIndex_dvd
import Theorems.Thm_LongGapsBetweenPrimes_prod_primeFactors_inv_sub_one

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (hP : Squarefree P) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) :
    assignmentVariance (fun p : PrimeIndex P => p.val) (tupleAssignment r) =
      ∏ i, 1 / ((r i).val.totient : ℝ) := by
  erw [assignmentVariance, tupleAssignment_prod r hpair (fun p _ => 1 / ((p.val : ℝ) - 1))]
  apply Finset.prod_congr rfl
  intro i _
  have hd := (Nat.mem_divisors.mp (r i).property).1
  have hsq : Squarefree (r i).val := fun q hq => hP q (hq.trans hd)
  rw [prod_primeIndex_dvd hP.ne_zero hd (fun p : ℕ => 1 / ((p : ℝ) - 1)),
    prod_primeFactors_inv_sub_one hsq]
end LongGapsBetweenPrimes
