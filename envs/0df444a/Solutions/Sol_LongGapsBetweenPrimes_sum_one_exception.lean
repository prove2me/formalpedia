-- Prove2me | solution 1 for LongGapsBetweenPrimes.sum_one_exception
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:10.002814+00:00
-- url     : https://prove2.me/submissions/ceed3402-cfe9-4848-9e11-02748dd53ebc

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p : ℕ} (a : Fin p) (c d : ℝ) :
    (∑ t : Fin p, if t = a then c else d) = c + ((p : ℝ) - 1) * d := by
  simp [Finset.sum_ite, Finset.filter_eq', Finset.filter_ne',
    Nat.cast_sub (Nat.succ_le_of_lt (Fin.pos a))]
end LongGapsBetweenPrimes
