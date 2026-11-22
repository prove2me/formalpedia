-- Prove2me | solution 1 for LongGapsBetweenPrimes.sum_residueFactor_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:48:52.8958+00:00
-- url     : https://prove2.me/submissions/77f6e32a-e2a0-46ac-81b0-5fb6600e131f

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sum_residueFactor

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p : ℕ} (hp : 1 < p) (a b : Fin p) (hab : a ≠ b) :
    (∑ t : Fin p, residueFactor a t * residueFactor b t) =
      -(p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  have hmul (t : Fin p) :
      residueFactor a t * residueFactor b t =
        (1 / ((p : ℝ) - 1)) * (residueFactor a t + residueFactor b t) -
          (1 / ((p : ℝ) - 1)) ^ 2 := by
    unfold residueFactor
    split_ifs with ha hb
    · exact (hab (ha.symm.trans hb)).elim
    all_goals ring
  simp_rw [hmul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
    sum_residueFactor hp a, sum_residueFactor hp b]
  simp
  ring
end LongGapsBetweenPrimes
