-- Prove2me | solution 1 for MethanolMuDrift.variability_shift
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:44:56.469769+00:00
-- url     : https://prove2.me/submissions/119fc643-931b-42ae-b5a3-9cb630292665

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

open MethanolMuDrift in
theorem solution :
    (8.80 : ℝ) - 8.32 = 0.48 ∧ Real.sqrt ((0.24 : ℝ) ^ 2 + 0.10 ^ 2) = 0.26 := by
  refine ⟨by norm_num, ?_⟩
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
  norm_num
