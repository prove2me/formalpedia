-- Prove2me | solution 1 for LongGapsBetweenPrimes.mem_auxiliaryPrimes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:55.170009+00:00
-- url     : https://prove2.me/submissions/daccd682-30d3-4ed1-813d-fad4e1e6d84e

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Z Y p : ℕ} :
    p ∈ auxiliaryPrimes Z Y ↔ p.Prime ∧ Z < p ∧ p ≤ Y := by
  simp only [auxiliaryPrimes, Finset.mem_sdiff, Nat.mem_primesLE, not_and_or, not_le]
  tauto
end LongGapsBetweenPrimes
