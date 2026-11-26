-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45MaskedFirstCellV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:09:29.841896+00:00
-- url     : https://prove2.me/submissions/3a8056ea-a09b-47f3-b41e-e4e0e728ec6c

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Right continuity at zero controls the first-cell error uniformly in the stopped clock. -/
theorem solution (Y : NNReal → ℝ) (T : NNReal) (K : ℝ)
    (hY : ContinuousWithinAt Y (Ici 0) 0) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t : NNReal,
      |K * (|Y (min t (T / (n : NNReal))) - Y 0|)| < δ := by
  intro δ hd
  have hY' : ContinuousAt Y 0 := by
    simpa only [show Ici (0 : NNReal) = univ by ext x; simp, continuousWithinAt_univ] using hY
  have hh := Metric.continuousAt_iff.mp hY' (δ/(|K|+1)) (by positivity)
  obtain ⟨r,hr,h⟩ := hh
  have hlim : Tendsto (fun n : ℕ => T / (n : NNReal)) atTop (nhds 0) := by
    exact tendsto_const_div_atTop_nhds_zero_nat T
  obtain ⟨N,hN⟩ := eventually_atTop.1
    (Metric.tendsto_nhds.mp hlim r hr)
  refine ⟨N,fun n hn t => ?_⟩
  have hq := hN n hn
  have hdist : dist (min t (T / (n : NNReal))) 0 < r :=
    (by
      change dist ((T / (n : NNReal) : NNReal) : ℝ) 0 < r at hq
      change dist ((min t (T / (n : NNReal)) : NNReal) : ℝ) 0 < r
      rw [Real.dist_eq,sub_zero,abs_of_nonneg (NNReal.coe_nonneg _)] at hq ⊢
      exact lt_of_le_of_lt (by exact_mod_cast min_le_right t (T / (n : NNReal))) hq)
  have hsmall := h hdist
  rw [Real.dist_eq] at hsmall
  rw [abs_mul,abs_abs]
  have hk : |K| < |K|+1 := by linarith
  calc
    _ ≤ (|K|+1) * |Y (min t (T / (n : NNReal))) - Y 0| :=
      mul_le_mul_of_nonneg_right hk.le (abs_nonneg _)
    _ < (|K|+1) * (δ/(|K|+1)) := mul_lt_mul_of_pos_left hsmall (by positivity)
    _ = δ := by field_simp
