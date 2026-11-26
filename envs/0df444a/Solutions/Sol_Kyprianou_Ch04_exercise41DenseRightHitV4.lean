-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41DenseRightHitV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:23:44.406013+00:00
-- url     : https://prove2.me/submissions/851c0bd9-de14-4dbb-95b2-09ea69a2359d

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (s : NNReal) (b e : ℝ) (hs : (s : ℝ) < b) (he : 0 < e)
    (hr : ContinuousWithinAt x (Ici s) s) (hz : x s = 0) :
    ∃ k : ℕ, s ≤ q k ∧ (q k : ℝ) < b ∧ |x (q k)| < e := by
  obtain ⟨r, hr0, hr'⟩ := Metric.continuousWithinAt_iff.mp hr e he
  let u : NNReal := s + Real.toNNReal (min r (b - (s : ℝ)) / 2)
  have hm : 0 < min r (b - (s : ℝ)) / 2 := by positivity
  have hu : (u : ℝ) = (s : ℝ) + min r (b - (s : ℝ)) / 2 := by
    simp [u, Real.coe_toNNReal _ hm.le]
  have hsu : s < u := by exact_mod_cast (show (s : ℝ) < (u : ℝ) by linarith)
  obtain ⟨v, hv⟩ := exists_between hsu
  obtain ⟨y, hy, ⟨k, hk⟩⟩ :=
    hq.inter_open_nonempty (Ioo s u) isOpen_Ioo ⟨v, hv⟩
  subst y
  have hsq : s ≤ q k := hy.1.le
  have hqr : (q k : ℝ) < (u : ℝ) := by exact_mod_cast hy.2
  have hq0 : (s : ℝ) ≤ (q k : ℝ) := by exact_mod_cast hsq
  have hdist : dist (q k) s < r := by
    change dist ((q k : ℝ)) (s : ℝ) < r
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hq0)]
    have := min_le_left r (b - (s : ℝ))
    linarith
  have hval := hr' hsq hdist
  rw [hz, Real.dist_eq, sub_zero] at hval
  refine ⟨k, hsq, ?_, hval⟩
  have := min_le_right r (b - (s : ℝ))
  linarith
