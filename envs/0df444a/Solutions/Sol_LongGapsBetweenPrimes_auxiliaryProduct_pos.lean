-- Prove2me | solution 1 for LongGapsBetweenPrimes.auxiliaryProduct_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:39:33.544108+00:00
-- url     : https://prove2.me/submissions/f2a9c6b6-a3c0-49e8-8656-a0aa116669e1

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_auxiliaryPrimes_prime

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (Z Y : ℕ) : 0 < auxiliaryProduct Z Y :=
  Finset.prod_pos (fun _ hp => (auxiliaryPrimes_prime hp).pos)
end LongGapsBetweenPrimes
