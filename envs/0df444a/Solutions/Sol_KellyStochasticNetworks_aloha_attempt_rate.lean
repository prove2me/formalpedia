-- Prove2me | solution 1 for KellyStochasticNetworks.aloha_attempt_rate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:18:54.508386+00:00
-- url     : https://prove2.me/submissions/7b014f32-7b7f-4b64-a745-1a9d61e024f1

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem ra_rate (f : ℝ) (hf : 0 < f) :
    (∀ t : ℕ, ackAttemptRate (alohaH f) (t + 1) = 1 + (t : ℝ) * f)
      ∧ Filter.Tendsto (fun t : ℕ => ackAttemptRate (alohaH f) t / Real.log t)
          Filter.atTop Filter.atTop := by
  have h1 : ∀ t : ℕ, ackAttemptRate (alohaH f) (t + 1) = 1 + (t : ℝ) * f := by
    intro t
    induction t with
    | zero => simp [ackAttemptRate, alohaH]
    | succ t ih =>
      unfold ackAttemptRate at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      have : alohaH f (t + 1 + 1) = f := by simp [alohaH]
      rw [this]; push_cast; ring
  refine ⟨h1, ?_⟩
  have hg : Filter.Tendsto (fun y : ℝ => (f * y + (1 - f)) / Real.log y) Filter.atTop
      Filter.atTop := by
    have h0 := Real.tendsto_pow_log_div_mul_add_atTop f (1 - f) 1 hf.ne'
    simp only [pow_one] at h0
    have hpos : ∀ᶠ y : ℝ in Filter.atTop, Real.log y / (f * y + (1 - f)) ∈ Set.Ioi 0 := by
      filter_upwards [Filter.eventually_gt_atTop 1] with y hy
      apply div_pos (Real.log_pos hy); nlinarith
    have h0' : Filter.Tendsto (fun y : ℝ => Real.log y / (f * y + (1 - f))) Filter.atTop
        (nhdsWithin 0 (Set.Ioi 0)) := tendsto_nhdsWithin_iff.mpr ⟨h0, hpos⟩
    refine h0'.inv_tendsto_nhdsGT_zero.congr (fun y => ?_)
    simp only [Pi.inv_apply, inv_div]
  have hc : Filter.Tendsto (fun t : ℕ => ((t:ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine (hg.comp hc).congr (fun t => ?_)
  simp only [Function.comp, h1]
  push_cast; ring

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution (f : ℝ) (hf : 0 < f) :
    (∀ t : ℕ, ackAttemptRate (alohaH f) (t + 1) = 1 + (t : ℝ) * f)
      ∧ Filter.Tendsto (fun t : ℕ => ackAttemptRate (alohaH f) t / Real.log t)
          Filter.atTop Filter.atTop := by
  exact ra_rate f hf
