-- Prove2me | solution 1 for MeasureTheory.tendsto_ball_div_volume_of_tendsto_closedBall_div_volume
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T22:32:13.949079+00:00
-- url     : https://prove2.me/submissions/0587f6d5-402e-4d9e-bc67-d1b1b26098de

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open MeasureTheory Filter Metric
open scoped ENNReal Topology

theorem solution (μ : Measure ℝ) (x : ℝ) (d : ℝ≥0∞)
    (h : Tendsto (fun r : ℝ => μ (closedBall x r) / volume (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    Tendsto (fun r : ℝ => μ (ball x r) / volume (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 d) := by
  have hid : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hs : Tendsto (fun r : ℝ => r / (1 + r)) (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · convert hid.div (tendsto_const_nhds.add hid)
        (by norm_num : (1 : ℝ) + 0 ≠ 0) using 1 <;>
          first | (ext r; rfl) | simp
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact div_pos hr (by linarith)
  have hc : Tendsto (fun r : ℝ => ENNReal.ofReal (1 / (1 + r)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have ht : Tendsto (fun r : ℝ => 1 / (1 + r)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      convert (tendsto_const_nhds (x := (1 : ℝ))).div (tendsto_const_nhds.add hid)
        (by norm_num : (1 : ℝ) + 0 ≠ 0) using 1 <;>
          first | (ext r; rfl) | simp
    simpa only [Function.comp_def, ENNReal.ofReal_one] using
      (ENNReal.continuous_ofReal.tendsto (1 : ℝ)).comp ht
  have hl := ENNReal.Tendsto.mul (h.comp hs) (Or.inr (by simp)) hc (Or.inl (by simp))
  simp only [mul_one] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl h
  · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have hp : 0 < 1 + r := by linarith
    have hsr : 0 < r / (1 + r) := div_pos hr hp
    have hlt : r / (1 + r) < r := (div_lt_iff₀ hp).mpr (by nlinarith)
    have he : ENNReal.ofReal (1 / (1 + r)) =
        volume (closedBall x (r / (1 + r))) / volume (ball x r) := by
      rw [Real.volume_closedBall, Real.volume_ball, ← ENNReal.ofReal_div_of_pos (by linarith : 0 < 2 * r)]
      congr 1
      field_simp
    simp only [Function.comp_def] at *
    rw [he, ← mul_div_assoc,
      ENNReal.div_mul_cancel (by simp [Real.volume_closedBall, hsr])
        (by rw [Real.volume_closedBall]; exact ENNReal.ofReal_ne_top)]
    exact ENNReal.div_le_div_right (measure_mono (closedBall_subset_ball hlt)) _
  · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [Real.volume_ball, Real.volume_closedBall]
    exact ENNReal.div_le_div_right (measure_mono ball_subset_closedBall) _
