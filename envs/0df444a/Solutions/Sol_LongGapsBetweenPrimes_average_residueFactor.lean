-- Prove2me | solution 1 for LongGapsBetweenPrimes.average_residueFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:50:48.797804+00:00
-- url     : https://prove2.me/submissions/43020d31-99bf-4cfd-bcb4-79557475cbc3

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sum_residueFactor

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p : ℕ} (hp : 1 < p) (a : Fin p) :
    Finset.expect Finset.univ (residueFactor a) = 0 := by
  simp [Finset.expect, sum_residueFactor hp]
end LongGapsBetweenPrimes
