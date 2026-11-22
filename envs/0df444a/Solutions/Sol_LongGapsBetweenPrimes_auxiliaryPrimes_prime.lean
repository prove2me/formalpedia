-- Prove2me | solution 1 for LongGapsBetweenPrimes.auxiliaryPrimes_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:52.999808+00:00
-- url     : https://prove2.me/submissions/02d006d2-7139-499a-8ce2-c899cb2f2523

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Z Y p : ℕ} (hp : p ∈ auxiliaryPrimes Z Y) : p.Prime :=
  (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
end LongGapsBetweenPrimes
