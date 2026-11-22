-- Prove2me | solution 1 for LongGapsBetweenPrimes.one_lt_of_mem_divisors_erase_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:53.418092+00:00
-- url     : https://prove2.me/submissions/945ba2db-aa06-41a5-bf21-41a42cc559a5

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P d : ℕ}
    (hd : d ∈ P.divisors.erase 1) : 1 < d := by
  exact lt_of_le_of_ne (Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase hd))
    (Finset.ne_of_mem_erase hd).symm
end LongGapsBetweenPrimes
