-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignmentProduct_tupleAssignment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:34.173498+00:00
-- url     : https://prove2.me/submissions/6886bc13-cccc-446b-89c0-938969cb0c77

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_prod_primeIndex_dvd
import Theorems.Thm_LongGapsBetweenPrimes_tupleProduct_dvd
import Theorems.Thm_LongGapsBetweenPrimes_tupleAssignment_isSome

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (hP : Squarefree P) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) :
    assignmentProduct (fun p : PrimeIndex P => p.val) (tupleAssignment r) = tupleProduct r := by
  classical
  unfold assignmentProduct assignmentSupport
  simp_rw [Finset.prod_filter, tupleAssignment_isSome]
  rw [prod_primeIndex_dvd hP.ne_zero (tupleProduct_dvd r hpair) (fun p => p),
    Nat.prod_primeFactors_of_squarefree
      (hP.squarefree_of_dvd (tupleProduct_dvd r hpair))]
end LongGapsBetweenPrimes
