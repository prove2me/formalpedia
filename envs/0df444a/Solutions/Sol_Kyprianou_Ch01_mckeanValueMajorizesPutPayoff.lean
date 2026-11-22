-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanValueMajorizesPutPayoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:33:00.660803+00:00
-- url     : https://prove2.me/submissions/7db136cb-a048-433f-a091-3e4bf756b2ec

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanBarrierGlobalMax

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (K phi y : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    max (K - Real.exp y) 0 ≤ mckeanValue K barrier phi y := by
  dsimp only
  let b : ℝ := Real.log (K * phi / (1 + phi))
  change max (K - Real.exp y) 0 ≤ mckeanValue K b phi y
  have hden : 0 < 1 + phi := by linarith
  have harg : 0 < K * phi / (1 + phi) :=
    div_pos (mul_pos hK hphi) hden
  have hexp : Real.exp b = K * phi / (1 + phi) :=
    Real.exp_log harg
  have hKb : Real.exp b ≤ K := by
    rw [hexp]
    apply (div_le_iff₀ hden).2
    nlinarith [hK]
  by_cases hy : b ≤ y
  · have hval : mckeanValue K b phi y =
        (K - Real.exp b) * Real.exp (-phi * (y - b)) := by
      simp [mckeanValue, not_lt.mpr hy]
    rw [hval]
    have hnonneg :
        0 ≤ (K - Real.exp b) * Real.exp (-phi * (y - b)) :=
      mul_nonneg (sub_nonneg.mpr hKb) (Real.exp_nonneg _)
    have hmax :=
      Kyprianou.Ch01.mckeanBarrierGlobalMax
        K phi y b y hK hphi rfl
    have hleft :
        (K - Real.exp y) * Real.exp (-phi * (y - y)) =
          K - Real.exp y := by simp
    rw [hleft] at hmax
    exact max_le hmax hnonneg
  · have hlt : y < b := lt_of_not_ge hy
    have hval : mckeanValue K b phi y = K - Real.exp y := by
      simp [mckeanValue, hlt]
    rw [hval]
    have hx : Real.exp y ≤ K :=
      (Real.exp_le_exp.mpr hlt.le).trans hKb
    exact max_le le_rfl (sub_nonneg.mpr hx)
