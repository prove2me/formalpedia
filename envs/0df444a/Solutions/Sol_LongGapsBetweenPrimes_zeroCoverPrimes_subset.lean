-- Prove2me | solution 1 for LongGapsBetweenPrimes.zeroCoverPrimes_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:28.461647+00:00
-- url     : https://prove2.me/submissions/48b494f3-586e-4ddb-841e-44cecfacd6b1

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) (hW : coverW x ≤ ⌊x⌋₊) :
    zeroCoverPrimes x ⊆ ⌊x⌋₊.primesLE := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hW, (Nat.mem_primesLE.mp hp).2⟩
  · have hm := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
    exact Nat.mem_primesLE.mpr ⟨hm.1.trans (Nat.floor_mono (by linarith : x / 2 ≤ x)), hm.2⟩
end LongGapsBetweenPrimes
