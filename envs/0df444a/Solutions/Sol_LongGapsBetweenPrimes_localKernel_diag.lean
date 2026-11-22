-- Prove2me | solution 1 for LongGapsBetweenPrimes.localKernel_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:51:32.109507+00:00
-- url     : https://prove2.me/submissions/ef334813-b7f6-4069-b21d-86958e168fce

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (p : ℕ) {k : ℕ} (i : Option (Fin k)) :
    localKernel p i i = 1 := by cases i <;> simp [localKernel]
end LongGapsBetweenPrimes
