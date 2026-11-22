-- Prove2me | solution 1 for LongGapsBetweenPrimes.continuous_divisorEulerMoment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:55:31.467437+00:00
-- url     : https://prove2.me/submissions/069ea29c-9f8c-456d-aefd-73c5cedae577

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (P : ℕ) :
    Continuous (fun t : ℝ => divisorEulerMoment P (-t)) := by
  unfold divisorEulerMoment
  apply continuous_finsetSum
  intro d hd
  have hdpos : 0 < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_mem_divisors hd)
  simp only [Real.rpow_def_of_pos hdpos]
  fun_prop
end LongGapsBetweenPrimes
