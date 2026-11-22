-- Prove2me | solution 1 for LongGapsBetweenPrimes.mem_assignmentPrimes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:34.556928+00:00
-- url     : https://prove2.me/submissions/aacf4e27-a60f-4b1b-beab-e7da4d422d66

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) (p : PrimeIndex P) :
    p.val ∈ assignmentPrimes σ ↔ (σ p).isSome := by
  classical
  simp [assignmentPrimes, assignmentSupport]
end LongGapsBetweenPrimes
