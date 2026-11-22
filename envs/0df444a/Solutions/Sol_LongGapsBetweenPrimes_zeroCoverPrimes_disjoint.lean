-- Prove2me | solution 1 for LongGapsBetweenPrimes.zeroCoverPrimes_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:37.283677+00:00
-- url     : https://prove2.me/submissions/dee05988-7bd0-4b80-b603-0e97a8ed85c0

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (x : ℝ) :
    Disjoint (zeroCoverPrimes x) (auxiliaryPrimes (coverW x) (coverZ x)) := by
  simp only [zeroCoverPrimes, auxiliaryPrimes, Finset.disjoint_left, Finset.mem_union,
    Finset.mem_sdiff]
  tauto
end LongGapsBetweenPrimes
