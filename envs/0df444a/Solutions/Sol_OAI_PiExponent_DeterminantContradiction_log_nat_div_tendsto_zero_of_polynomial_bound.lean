-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.log_nat_div_tendsto_zero_of_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:09:37.010354+00:00
-- url     : https://prove2.me/submissions/975d5d95-b3ec-496d-81a6-d13aeadf9fe1

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology

theorem solution (f : ℝ → ℕ) (N : ℕ) (C : ℝ) (hC : 0 < C)
    (hpos : ∀ᶠ H : ℝ in atTop, 1 ≤ (f H : ℝ))
    (hbound : ∀ᶠ H : ℝ in atTop, (f H : ℝ) ≤ C * (H + 1) ^ N) :
    Tendsto (fun H : ℝ => Real.log (f H : ℝ) / H) atTop (𝓝 0) := by
  -- `log x / x → 0` and its shift: `log (H + 1) / H → 0`.
  have hlog_shift : Tendsto (fun H : ℝ => Real.log (H + 1) / H) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / (1 * x + (-1))) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
    have hcomp := h0.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
    simpa [Function.comp_def] using hcomp
  -- The eventual upper bound tends to zero.
  have hupper : Tendsto (fun H : ℝ => Real.log C / H + (N : ℝ) * (Real.log (H + 1) / H))
      atTop (𝓝 0) := by
    have hc : Tendsto (fun H : ℝ => Real.log C / H) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using hc.add (hlog_shift.const_mul (N : ℝ))
  -- Squeeze between 0 and the upper bound.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [hpos, eventually_gt_atTop (0 : ℝ)] with H hp hH
    exact div_nonneg (Real.log_nonneg hp) hH.le
  · filter_upwards [hpos, hbound, eventually_gt_atTop (0 : ℝ)] with H hp hb hH
    have hfpos : (0 : ℝ) < (f H : ℝ) := lt_of_lt_of_le zero_lt_one hp
    have hH1 : (0 : ℝ) < H + 1 := by linarith
    have hpow : (0 : ℝ) < (H + 1) ^ N := pow_pos hH1 N
    have hlog_le : Real.log (f H : ℝ) ≤ Real.log C + (N : ℝ) * Real.log (H + 1) := by
      calc Real.log (f H : ℝ) ≤ Real.log (C * (H + 1) ^ N) := Real.log_le_log hfpos hb
        _ = Real.log C + Real.log ((H + 1) ^ N) := Real.log_mul hC.ne' hpow.ne'
        _ = Real.log C + (N : ℝ) * Real.log (H + 1) := by rw [Real.log_pow]
    have hdiv := div_le_div_of_nonneg_right hlog_le hH.le
    rwa [add_div, mul_div_assoc] at hdiv
