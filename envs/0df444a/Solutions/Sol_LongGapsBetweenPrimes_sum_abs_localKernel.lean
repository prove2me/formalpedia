-- Prove2me | solution 1 for LongGapsBetweenPrimes.sum_abs_localKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:51:36.267747+00:00
-- url     : https://prove2.me/submissions/4250aa1d-0ca2-4d26-84c7-a4348eb341a7

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sum_one_exception

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p k : ℕ} (hp : 1 < p) (i : Option (Fin k)) :
    (∑ j, |localKernel p i j|) = localRow p k i := by
  have hpR : 0 ≤ (p : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hp.le)
  cases i with
  | none => simp [localKernel, localRow, Fintype.sum_option]
  | some a =>
      simp only [Fintype.sum_option, localKernel, abs_zero, zero_add, apply_ite abs,
        abs_one, abs_div, abs_neg, abs_of_nonneg hpR]
      simpa [localRow, eq_comm, div_eq_mul_inv] using
        sum_one_exception a 1 (1 / ((p : ℝ) - 1))
end LongGapsBetweenPrimes
