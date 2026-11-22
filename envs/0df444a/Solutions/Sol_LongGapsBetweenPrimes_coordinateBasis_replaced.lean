-- Prove2me | solution 1 for LongGapsBetweenPrimes.coordinateBasis_replaced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:06:47.049746+00:00
-- url     : https://prove2.me/submissions/714c4dfd-b411-4dea-b8de-c5f3c0b75c04

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_prod_primeIndex_dvd
import Theorems.Thm_LongGapsBetweenPrimes_prod_primeFactors_inv_sub_one

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (hP : Squarefree P)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (i j : Fin k)
    (d : DivisorIndex P) (t : (p : PrimeIndex P) → Fin p.val) :
    coordinateBasis (fun p => replacedLocalBasis (root p) i) d j t =
      if j = i then 1 / (d.val.totient : ℝ) else
        coordinateBasis (fun p => rawLocalBasis (root p)) d j t := by
  classical
  by_cases h : j = i
  · simp only [coordinateBasis, replacedLocalBasis, if_pos h]
    rw [prod_primeIndex_dvd hP.ne_zero (Nat.dvd_of_mem_divisors d.property)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)),
      prod_primeFactors_inv_sub_one
        (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors d.property))]
  · simp [coordinateBasis, replacedLocalBasis, rawLocalBasis, h]
end LongGapsBetweenPrimes
