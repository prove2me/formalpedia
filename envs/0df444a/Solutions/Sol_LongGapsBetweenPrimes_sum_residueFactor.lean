-- Prove2me | solution 1 for LongGapsBetweenPrimes.sum_residueFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:36:12.463639+00:00
-- url     : https://prove2.me/submissions/f7f81f4f-2baa-4f4d-8679-3c2df233778e

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sum_one_exception

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p : ℕ} (hp : 1 < p) (a : Fin p) :
    ∑ t : Fin p, residueFactor a t = 0 := by
  have hp' : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ne_of_gt hp)
  simp [residueFactor, sum_one_exception, hp']
end LongGapsBetweenPrimes
