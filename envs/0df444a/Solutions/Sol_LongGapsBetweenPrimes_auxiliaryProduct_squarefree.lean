-- Prove2me | solution 1 for LongGapsBetweenPrimes.auxiliaryProduct_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:54:52.366305+00:00
-- url     : https://prove2.me/submissions/72a79d8c-50a8-4d54-aa74-bc0f972285e7

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_auxiliaryPrimes_prime

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (Z Y : ℕ) : Squarefree (auxiliaryProduct Z Y) := by
  exact Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (auxiliaryPrimes_prime hp) (auxiliaryPrimes_prime hq)).mpr hpq))
    (fun p hp => (auxiliaryPrimes_prime hp).squarefree)
end LongGapsBetweenPrimes
