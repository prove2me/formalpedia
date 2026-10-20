-- Prove2me | solution 1 for HardyLittlewood.tuple_integral_diverges
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:57:41.781553+00:00
-- url     : https://prove2.me/submissions/9e4f0dc6-3297-4682-8f45-a4f45c5a819e

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

open HardyLittlewood

theorem solution (k : ℕ) :
    Filter.Tendsto (fun n => ∫ t in (2:ℝ)..(n:ℝ), 1 / (Real.log t) ^ (k + 1))
      Filter.atTop Filter.atTop := by
  -- lower bound (n-2)/(log n)^(k+1)
  have hlow : ∀ n : ℝ, 3 ≤ n → ((n:ℝ) - 2) / (Real.log n) ^ (k+1) ≤
      ∫ t in (2:ℝ)..(n:ℝ), 1 / (Real.log t) ^ (k + 1) := by
    intro n hn
    have hn' : (3:ℝ) ≤ n := hn
    have hcont : ContinuousOn (fun t : ℝ => 1 / (Real.log t) ^ (k + 1)) (Set.uIcc 2 n) := by
      rw [Set.uIcc_of_le (by linarith)]
      apply ContinuousOn.div continuousOn_const
      · exact (Real.continuousOn_log.mono (fun x hx => by
          simp only [Set.mem_Icc] at hx; simp; linarith [hx.1])).pow _
      · intro x hx; simp only [Set.mem_Icc] at hx
        have : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
        positivity
    have h1 : ∫ t in (2:ℝ)..(n:ℝ), (1 / (Real.log n) ^ (k+1)) ≤
        ∫ t in (2:ℝ)..(n:ℝ), 1 / (Real.log t) ^ (k + 1) := by
      apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (hcont.intervalIntegrable)
      intro x hx
      have hx0 : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ hx0.le (Real.log_le_log (by linarith [hx.1]) hx.2) _
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    calc ((n:ℝ) - 2) / (Real.log n) ^ (k+1) = ((n:ℝ) - 2) * (1 / (Real.log n) ^ (k+1)) := by ring
      _ ≤ _ := h1
  have hlim : Filter.Tendsto (fun x : ℝ => (x - 2) / (Real.log x) ^ (k+1)) Filter.atTop Filter.atTop := by
    have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) (k+1) one_ne_zero
    have hpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < Real.log x ^ (k+1) / (1 * x + -2) := by
      filter_upwards [Filter.eventually_gt_atTop 3] with x hx
      have : 0 < Real.log x := Real.log_pos (by linarith)
      have : 0 < 1 * x + -2 := by linarith
      positivity
    have h2 := (tendsto_nhdsWithin_iff.mpr ⟨h0, hpos⟩).inv_tendsto_nhdsGT_zero
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 3] with x hx
    simp only [Pi.inv_apply, inv_div]; ring_nf
  refine Filter.tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn
  exact hlow n hn
