-- Prove2me | solution 1 for OAI.PiExponent.log_nat_function_div_tendsto_zero_of_eventual_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:09:01.385014+00:00
-- url     : https://prove2.me/submissions/e18536e7-3780-4b12-a01b-e928386d28c1

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

theorem solution (f : ℝ → ℕ) (C : ℝ) (p : ℕ) (hC : 0 < C)
    (hbound : ∀ᶠ H : ℝ in atTop, 1 ≤ f H ∧ (f H : ℝ) ≤ C * (H + 1) ^ p) :
    Tendsto (fun H : ℝ => Real.log (f H : ℝ) / H) atTop (𝓝 0) := by
  -- `log x / x → 0` and its shift: `log (H + 1) / H → 0`.
  have hlog_shift : Tendsto (fun H : ℝ => Real.log (H + 1) / H) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / (1 * x + (-1))) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
    have hcomp := h0.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
    simpa [Function.comp_def] using hcomp
  -- The eventual upper bound tends to zero.
  have hupper : Tendsto (fun H : ℝ => Real.log C / H + (p : ℝ) * (Real.log (H + 1) / H))
      atTop (𝓝 0) := by
    have hc : Tendsto (fun H : ℝ => Real.log C / H) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using hc.add (hlog_shift.const_mul (p : ℝ))
  -- Squeeze between 0 and the upper bound.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with H hb hH
    obtain ⟨hf1, -⟩ := hb
    have h1 : (1 : ℝ) ≤ (f H : ℝ) := by exact_mod_cast hf1
    exact div_nonneg (Real.log_nonneg h1) hH.le
  · filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with H hb hH
    obtain ⟨hf1, hfN⟩ := hb
    have hfpos : (0 : ℝ) < (f H : ℝ) := by exact_mod_cast hf1
    have hH1 : (0 : ℝ) < H + 1 := by linarith
    have hpow : (0 : ℝ) < (H + 1) ^ p := pow_pos hH1 p
    have hlog_le : Real.log (f H : ℝ) ≤ Real.log C + (p : ℝ) * Real.log (H + 1) := by
      calc Real.log (f H : ℝ) ≤ Real.log (C * (H + 1) ^ p) := Real.log_le_log hfpos hfN
        _ = Real.log C + Real.log ((H + 1) ^ p) := Real.log_mul hC.ne' hpow.ne'
        _ = Real.log C + (p : ℝ) * Real.log (H + 1) := by rw [Real.log_pow]
    have hdiv := div_le_div_of_nonneg_right hlog_le hH.le
    rwa [add_div, mul_div_assoc] at hdiv
