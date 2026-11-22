-- Prove2me | solution 1 for LongGapsBetweenPrimes.average_residueFactor_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:51:18.83627+00:00
-- url     : https://prove2.me/submissions/abf9ed2c-1e14-48fb-986e-dfd52ced59c0

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sum_residueFactor_mul

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p : ℕ} (hp : 1 < p) (a b : Fin p) (hab : a ≠ b) :
    Finset.expect Finset.univ (fun t => residueFactor a t * residueFactor b t) =
      -1 / ((p : ℝ) - 1) ^ 2 := by
  have hp0 : p ≠ 0 := by omega
  simp [Finset.expect_eq_sum_div_card, sum_residueFactor_mul hp a b hab,
    div_eq_mul_inv, mul_right_comm, hp0]
end LongGapsBetweenPrimes
