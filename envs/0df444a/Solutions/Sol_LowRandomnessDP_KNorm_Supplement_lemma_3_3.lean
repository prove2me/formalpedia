-- Prove2me | solution 1 for LowRandomnessDP.KNorm.Supplement.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:13:42.927096+00:00
-- url     : https://prove2.me/submissions/8ba53503-bebc-4572-8c99-1d0d0034da31

import Mathlib
import Definitions.Def_LowRandomnessDP_KNorm_Supplement_Rounding

open LowRandomnessDP.KNorm LowRandomnessDP.KNorm.Supplement

theorem solution (d : ℕ) (hd : 0 < d) (x : Vec d) :
    ∀ i, |R hd x i - x i| ≤ 1 := by
  intro i
  have h1 := Int.floor_le (x i - ((A hd x).val : ℝ) / d)
  have h2 := Int.lt_floor_add_one (x i - ((A hd x).val : ℝ) / d)
  unfold R
  rw [abs_le]
  constructor <;> linarith
