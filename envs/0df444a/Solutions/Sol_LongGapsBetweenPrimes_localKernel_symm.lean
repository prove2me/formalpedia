-- Prove2me | solution 1 for LongGapsBetweenPrimes.localKernel_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:51:29.473814+00:00
-- url     : https://prove2.me/submissions/7102d5b1-f0a4-4f56-8e3e-59af67dbcc93

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (p : ℕ) {k : ℕ} (i j : Option (Fin k)) :
    localKernel p i j = localKernel p j i := by
  cases i <;> cases j <;> simp [localKernel, eq_comm]
end LongGapsBetweenPrimes
