-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanValueBoundedNonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:42:10.584126+00:00
-- url     : https://prove2.me/submissions/d0039abb-9bba-4e8f-bac1-6d47947f5b97

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanValueMajorizesPutPayoff

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (K phi y : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    0 ≤ mckeanValue K barrier phi y ∧
      mckeanValue K barrier phi y ≤ K := by
  dsimp only
  let b : ℝ := Real.log (K * phi / (1 + phi))
  change 0 ≤ mckeanValue K b phi y ∧
    mckeanValue K b phi y ≤ K
  have hm := Kyprianou.Ch01.mckeanValueMajorizesPutPayoff
    K phi y hK hphi
  change max (K - Real.exp y) 0 ≤ mckeanValue K b phi y at hm
  refine ⟨(le_max_right _ _).trans hm, ?_⟩
  have hden : 0 < 1 + phi := by linarith
  have harg : 0 < K * phi / (1 + phi) :=
    div_pos (mul_pos hK hphi) hden
  have hKb : Real.exp b ≤ K := by
    change Real.exp (Real.log (K * phi / (1 + phi))) ≤ K
    rw [Real.exp_log harg]
    apply (div_le_iff₀ hden).2
    nlinarith [hK]
  by_cases hy : y < b
  · simp only [mckeanValue, if_pos hy]
    linarith [Real.exp_pos y]
  · have hge : 0 ≤ y - b := sub_nonneg.mpr (le_of_not_gt hy)
    have he : Real.exp (-phi * (y - b)) ≤ 1 := by
      have hle : -phi * (y - b) ≤ 0 := by nlinarith [mul_nonneg hphi.le hge]
      simpa using Real.exp_le_exp.mpr hle
    simp only [mckeanValue, if_neg hy]
    have hc := mul_le_mul_of_nonneg_left he (sub_nonneg.mpr hKb)
    linarith [Real.exp_nonneg b]
