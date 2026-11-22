-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_drawdown_singleton_markov
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T01:39:46.84848+00:00
-- url     : https://prove2.me/submissions/34331b4c-1468-482e-a8c0-c03777c14fe6

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_singleton_split_le
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Iio (0 : ℝ)) = 0) (x : ℝ) (hx : 0 < x) :
    μ {x} ≤ ENNReal.ofReal (1 - Real.exp (-x))⁻¹ *
      (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ)) := by
  let c := ENNReal.ofReal (1 - Real.exp (-x))
  let b := ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ
  have h : μ {x} * c + b ≤ 1 :=
    Kyprianou.Ch08.StageB.p2m81_drawdown_singleton_split_le μ hsupp x hx
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    ((le_add_left (le_refl b)).trans h)
  have hc : c ≠ 0 := by
    have he : Real.exp (-x) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr he))
  have hh : μ {x} * c ≤ 1 - b := by
    have hm := tsub_le_tsub_right h b
    simpa only [ENNReal.add_sub_cancel_right hb] using hm
  have result : μ {x} ≤ (1 - b) / c :=
    (ENNReal.le_div_iff_mul_le (Or.inl hc) (Or.inl ENNReal.ofReal_ne_top)).mpr hh
  have hpos : 0 < 1 - Real.exp (-x) := by
    apply sub_pos.mpr
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  rw [ENNReal.ofReal_inv_of_pos hpos]
  simpa only [c, b, div_eq_mul_inv, mul_comm] using result
