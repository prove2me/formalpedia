-- Prove2me | solution 1 for HighEntropyLimit.classical_sub_quantum_entropy_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:41:32.620167+00:00
-- url     : https://prove2.me/submissions/1c0fdcd4-1e36-47cd-a294-5820efb5a45e

import Mathlib
import Definitions.Def_HighEntropyLimit_gaussian_entropy

open Filter Topology HighEntropyLimit

lemma F_tendsto :
    Tendsto (fun s : ℝ => (1 - s * Real.log ((s + 1 / 2) / (s - 1 / 2))) -
      1 / 2 * Real.log ((s - 1 / 2) * (s + 1 / 2) / s ^ 2)) atTop (𝓝 0) := by
  have hA : Tendsto (fun s : ℝ => 1 - s * Real.log ((s + 1 / 2) / (s - 1 / 2))) atTop (𝓝 0) := by
    have hlo : Tendsto (fun s : ℝ => -(1 / (2 * s - 1))) atTop (𝓝 0) := by
      have : Tendsto (fun s : ℝ => 2 * s - 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop two_pos)
      have h := (tendsto_inv_atTop_zero.comp this).neg
      rw [neg_zero] at h
      refine h.congr (fun s => ?_)
      simp
    have hhi : Tendsto (fun s : ℝ => 1 / (2 * s + 1)) atTop (𝓝 0) := by
      have : Tendsto (fun s : ℝ => 2 * s + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop two_pos)
      refine (tendsto_inv_atTop_zero.comp this).congr (fun s => ?_)
      simp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [eventually_gt_atTop 1] with s hs
      have ha : 0 < s - 1 / 2 := by linarith
      have hb : 0 < s + 1 / 2 := by linarith
      have ha' : s - 1 / 2 ≠ 0 := ha.ne'
      have hc : 2 * s - 1 ≠ 0 := (by linarith : (0:ℝ) < 2 * s - 1).ne'
      have h1 : Real.log ((s + 1 / 2) / (s - 1 / 2)) ≤ (s + 1 / 2) / (s - 1 / 2) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hb ha)
      have h2 : (s + 1 / 2) / (s - 1 / 2) - 1 = 1 / (s - 1 / 2) := by
        rw [div_sub_one ha']; congr 1; ring
      rw [h2] at h1
      have h3 : s * Real.log ((s + 1 / 2) / (s - 1 / 2)) ≤ s * (1 / (s - 1 / 2)) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      have h4 : 1 - s * (1 / (s - 1 / 2)) = -(1 / (2 * s - 1)) := by
        have e : ∀ t : ℝ, t ≠ 0 → 1 - (t + 1 / 2) * (1 / t) = -(1 / (2 * t)) := by
          intro t ht; field_simp; ring
        have := e (s - 1 / 2) ha'
        rwa [show s - 1 / 2 + 1 / 2 = s by ring, show 2 * (s - 1 / 2) = 2 * s - 1 by ring] at this
      linarith
    · filter_upwards [eventually_gt_atTop 1] with s hs
      have ha : 0 < s - 1 / 2 := by linarith
      have hb : 0 < s + 1 / 2 := by linarith
      have hb' : s + 1 / 2 ≠ 0 := hb.ne'
      have hc : 2 * s + 1 ≠ 0 := (by linarith : (0:ℝ) < 2 * s + 1).ne'
      have h1 : Real.log ((s - 1 / 2) / (s + 1 / 2)) ≤ (s - 1 / 2) / (s + 1 / 2) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos ha hb)
      have h1' : Real.log ((s + 1 / 2) / (s - 1 / 2)) = -Real.log ((s - 1 / 2) / (s + 1 / 2)) := by
        rw [← Real.log_inv, inv_div]
      have h2 : (s - 1 / 2) / (s + 1 / 2) - 1 = -(1 / (s + 1 / 2)) := by
        rw [div_sub_one hb', ← neg_div]; congr 1; ring
      rw [h2] at h1
      rw [h1']
      have h3 : s * (1 / (s + 1 / 2)) ≤ s * -Real.log ((s - 1 / 2) / (s + 1 / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have h4 : 1 - s * (1 / (s + 1 / 2)) = 1 / (2 * s + 1) := by
        have e : ∀ t : ℝ, t ≠ 0 → 1 - (t - 1 / 2) * (1 / t) = 1 / (2 * t) := by
          intro t ht; field_simp; ring
        have := e (s + 1 / 2) hb'
        rwa [show s + 1 / 2 - 1 / 2 = s by ring, show 2 * (s + 1 / 2) = 2 * s + 1 by ring] at this
      linarith
  have hB : Tendsto (fun s : ℝ => 1 / 2 * Real.log ((s - 1 / 2) * (s + 1 / 2) / s ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => 1 - 1 / 4 * (s ^ 2)⁻¹) atTop (𝓝 1) := by
      have : Tendsto (fun s : ℝ => (s ^ 2)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)
      have h := (this.const_mul (1 / 4)).const_sub 1
      rw [mul_zero, sub_zero] at h
      exact h
    have h2 := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    rw [Real.log_one] at h2
    have h3 := h2.const_mul (1 / 2)
    rw [mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with s hs
    simp only [Function.comp]
    congr 2
    field_simp; ring
  simpa using hA.sub hB

theorem solution (hbar : ℝ) (hhbar : 0 < hbar) :
    Tendsto (fun Sig : ℝ => classicalGaussianEntropy hbar Sig - quantumGaussianEntropy hbar Sig)
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun Sig : ℝ => Sig / hbar) atTop atTop := tendsto_id.atTop_div_const hhbar
  refine (F_tendsto.comp h1).congr' ?_
  filter_upwards [h1.eventually (eventually_gt_atTop 1)] with Sig hs
  simp only [Function.comp, classicalGaussianEntropy, quantumGaussianEntropy]
  set s := Sig / hbar
  have ha : 0 < s - 1 / 2 := by linarith
  have hb : 0 < s + 1 / 2 := by linarith
  have hs0 : 0 < s := by linarith
  rw [Real.log_div hb.ne' ha.ne', Real.log_div (mul_pos ha hb).ne' (by positivity),
    Real.log_mul ha.ne' hb.ne', Real.log_pow]
  push_cast
  ring
