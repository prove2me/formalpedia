-- Prove2me | solution 1 for LongGapsBetweenPrimes.diagonalMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:31.850232+00:00
-- url     : https://prove2.me/submissions/61113832-9fe9-4205-9168-836f06e683c4

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_tupleMass_nonneg

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (P k : ℕ) (D : ℝ) : 0 ≤ diagonalMass P k D :=
  Finset.sum_nonneg (fun r _ => tupleMass_nonneg r)
end LongGapsBetweenPrimes
