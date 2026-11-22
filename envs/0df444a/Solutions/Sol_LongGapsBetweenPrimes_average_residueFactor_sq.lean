-- Prove2me | solution 1 for LongGapsBetweenPrimes.average_residueFactor_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:51:02.565617+00:00
-- url     : https://prove2.me/submissions/118d0c27-423b-4c1c-ba87-4f1379796531

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sum_residueFactor_sq

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p : ℕ} (hp : 1 < p) (a : Fin p) :
    Finset.expect Finset.univ (fun t => residueFactor a t ^ 2) = 1 / ((p : ℝ) - 1) := by
  have hp0 : p ≠ 0 := by omega
  simp [Finset.expect_eq_sum_div_card, sum_residueFactor_sq hp, div_eq_mul_inv,
    mul_right_comm, hp0]
end LongGapsBetweenPrimes
