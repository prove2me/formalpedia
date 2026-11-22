-- Prove2me | solution 1 for LongGapsBetweenPrimes.residue_average_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:53:24.91281+00:00
-- url     : https://prove2.me/submissions/9b8061ee-a92f-4817-b31c-a334808893c7

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_residue_count_error_le_one

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {m a T : ℕ} (ha : a < m) (hT : 0 < T) :
    |(∑ n ∈ Finset.range T, residueIndicator m a n) / (T : ℝ) - 1 / (m : ℝ)| ≤
      1 / (T : ℝ) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have he : (∑ n ∈ Finset.range T, residueIndicator m a n) / (T : ℝ) - 1 / (m : ℝ) =
      ((∑ n ∈ Finset.range T, residueIndicator m a n) - (T : ℝ) / m) / T := by
    field_simp [ne_of_gt hTr]
  rw [he, abs_div, abs_of_pos hTr]
  exact div_le_div_of_nonneg_right (residue_count_error_le_one ha T) hTr.le
end LongGapsBetweenPrimes
