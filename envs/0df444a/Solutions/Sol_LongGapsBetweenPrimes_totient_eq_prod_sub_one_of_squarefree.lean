-- Prove2me | solution 1 for LongGapsBetweenPrimes.totient_eq_prod_sub_one_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:48:55.852812+00:00
-- url     : https://prove2.me/submissions/b48941d1-1c34-4a10-a035-d8e52e6030ab

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {d : ℕ} (hd : Squarefree d) :
    d.totient = ∏ p ∈ d.primeFactors, (p - 1) := by
  have h := Nat.totient_mul_prod_primeFactors d
  rw [Nat.prod_primeFactors_of_squarefree hd] at h
  exact mul_right_cancel₀ hd.ne_zero (h.trans (mul_comm _ _))
end LongGapsBetweenPrimes
