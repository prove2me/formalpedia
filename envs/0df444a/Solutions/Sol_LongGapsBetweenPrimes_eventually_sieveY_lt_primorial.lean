-- Prove2me | solution 1 for LongGapsBetweenPrimes.eventually_sieveY_lt_primorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:05.053135+00:00
-- url     : https://prove2.me/submissions/921e230e-4f82-4e1c-af47-21a39504fd10

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : ∀ᶠ x : ℝ in Filter.atTop,
    sieveY x < primorial ⌊x⌋₊ := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hpower : Filter.Tendsto (fun x : ℝ => 1 / (Real.log x) ^ 5)
      Filter.atTop (nhds 0) := by
    simpa [one_div] using
      ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp Real.tendsto_log_atTop).pow 5
  have hconstant : Filter.Tendsto (fun x : ℝ => Real.log 2 / x)
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop Filter.tendsto_id
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log (x + 2) / x)
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop 2 Filter.tendsto_id)
  have hsqrt : Filter.Tendsto (fun x : ℝ => C / Real.sqrt x)
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hsmall := ((hpower.add hconstant).add hlog).add hsqrt
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
    hsmall.eventually_lt_const (by simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    with x hx hsmall
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hpower_eq : 1 / (Real.log x) ^ 5 = sieveUpperLog x / x := by
    rw [sieveUpperLog, div_right_comm, div_self hx0.ne']
  have hsqrt_eq : C / Real.sqrt x = C * Real.sqrt x / x := by
    apply (div_eq_div_iff (Real.sqrt_pos.mpr hx0).ne' hx0.ne').mpr
    rw [mul_assoc, Real.mul_self_sqrt hx0.le]
  rw [hpower_eq, hsqrt_eq, ← add_div, ← add_div, ← add_div] at hsmall
  have htheta : sieveUpperLog x < Chebyshev.theta x := by
    have hbound := (div_lt_iff₀ hx0).mp hsmall
    linarith [Chebyshev.psi_ge' hx0.le, hC x]
  unfold sieveY
  apply (Nat.floor_lt (Real.exp_pos _).le).mpr
  calc
    Real.exp (sieveUpperLog x) < Real.exp (Chebyshev.theta x) :=
      Real.exp_lt_exp.mpr htheta
    _ = (primorial ⌊x⌋₊ : ℝ) := by
      rw [Chebyshev.theta_eq_log_primorial, Real.exp_log (by
        exact_mod_cast primorial_pos ⌊x⌋₊)]
end LongGapsBetweenPrimes
