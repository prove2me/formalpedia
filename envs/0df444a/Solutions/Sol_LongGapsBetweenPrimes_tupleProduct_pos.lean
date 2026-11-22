-- Prove2me | solution 1 for LongGapsBetweenPrimes.tupleProduct_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:15.523321+00:00
-- url     : https://prove2.me/submissions/2f07a64b-a9be-47d2-89a5-3b780da78dd1

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (r : DivisorTuple P k) : 0 < tupleProduct r := by
  exact Finset.prod_pos fun i _ => Nat.pos_of_mem_divisors (r i).property
end LongGapsBetweenPrimes
