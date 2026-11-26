-- Prove2me | solution 1 for Kyprianou.Ch04.rationalSlopeAtInteriorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:44:58.462409+00:00
-- url     : https://prove2.me/submissions/39861eeb-6003-4319-9ccc-0345c3aa7da0

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal
set_option autoImplicit false

/-- Differentiability at a nonnegative real time yields the rational shifted slope limit. -/
theorem solution (x : ℝ≥0 → ℝ) (d s : ℝ) (hs : 0 ≤ s)
    (hd : HasDerivAt (fun t : ℝ => x (Real.toNNReal t)) d s) :
    Tendsto (fun r : ℚ =>
      (x (Real.toNNReal s + Real.toNNReal (r : ℝ)) - x (Real.toNNReal s)) /
        (Real.toNNReal (r : ℝ) : ℝ))
      (nhdsWithin (0 : ℚ) (Ioi 0)) (nhds d) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.tendsto_nhdsWithin_nhds.mp hd.tendsto_slope_zero_right ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  have hdist : dist (r : ℝ) 0 < δ := by simpa only [Rat.dist_eq, Real.dist_eq, Rat.cast_zero] using hrδ
  have h := hb (show (r : ℝ) ∈ Ioi 0 from hr0) hdist
  have hsum : Real.toNNReal (s + (r : ℝ)) = Real.toNNReal s + Real.toNNReal (r : ℝ) := by
    apply NNReal.eq
    rw [NNReal.coe_add, Real.coe_toNNReal _ (add_nonneg hs hr0.le),
      Real.coe_toNNReal _ hs, Real.coe_toNNReal _ hr0.le]
  simpa only [hsum, Real.coe_toNNReal _ hr0.le, smul_eq_mul, div_eq_mul_inv, mul_comm] using h
