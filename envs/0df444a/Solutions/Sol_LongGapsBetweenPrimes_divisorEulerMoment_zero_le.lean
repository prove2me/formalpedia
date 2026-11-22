-- Prove2me | solution 1 for LongGapsBetweenPrimes.divisorEulerMoment_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:10.035581+00:00
-- url     : https://prove2.me/submissions/16f6c593-a1a9-4ea7-b7b7-5de122ac92b8

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_log_le_eulerProduct_one
import Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_one_le
import Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_nonneg
import Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_zero_factorization

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Z Y : ℕ} (hZY : Z ≤ Y) (hZ : 2 ≤ Z) :
    divisorEulerMoment (auxiliaryProduct Z Y) 0 ≤
      Real.exp 6 * (1 + Real.log Y) / Real.log Z := by
  have hlog : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  apply (le_div_iff₀ hlog).mpr
  calc
    _ ≤ divisorEulerMoment (auxiliaryProduct Z Y) 0 * eulerProduct Z 1 :=
      mul_le_mul_of_nonneg_left (log_le_eulerProduct_one Z) (divisorEulerMoment_nonneg _ _)
    _ = eulerProduct Y 1 := divisorEulerMoment_zero_factorization hZY
    _ ≤ Real.exp 6 * (1 + Real.log Y) := eulerProduct_one_le (hZ.trans hZY)
end LongGapsBetweenPrimes
