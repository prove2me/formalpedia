-- Prove2me | solution 1 for LongGapsBetweenPrimes.prod_primeFactors_inv_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:50:03.482042+00:00
-- url     : https://prove2.me/submissions/07030651-7f63-4fe2-8db3-3320a765bed9

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_totient_eq_prod_sub_one_of_squarefree

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {d : ℕ} (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 1)) = 1 / (d.totient : ℝ) := by
  rw [Finset.prod_div_distrib, Finset.prod_const_one,
    totient_eq_prod_sub_one_of_squarefree hd, Nat.cast_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
end LongGapsBetweenPrimes
