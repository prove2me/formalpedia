-- Prove2me | solution 1 for LongGapsBetweenPrimes.sum_residueFactor_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:48:48.01902+00:00
-- url     : https://prove2.me/submissions/b0867407-e157-4265-bd7c-1e59eff21e16

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sum_one_exception

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p : ℕ} (hp : 1 < p) (a : Fin p) :
    (∑ t : Fin p, (residueFactor a t) ^ 2) = (p : ℝ) / ((p : ℝ) - 1) := by
  have hp' : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ne_of_gt hp)
  simp only [residueFactor, ite_pow, neg_one_sq, sum_one_exception]
  field_simp
  ring
end LongGapsBetweenPrimes
