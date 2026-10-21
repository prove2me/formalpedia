-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.analyticColumn_unweighted_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:32:26.135666+00:00
-- url     : https://prove2.me/submissions/52d6e813-d581-438a-a79d-96e47cf9c356

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analyticColumn_binomial_product_bound
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analyticColumn_exponential_factor_bound
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analyticColumn_power_factor_bound

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (h : ℕ) (a A : Fin m → ℕ)
    {R : ℝ} (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖analyticColumn h a A z‖ ≤
      Real.exp ((h : ℝ) * R +
        (∑ i, (a i : ℝ)) * Real.log (2 * R)) := by
  have hc := OAI.PiExponent.FinitePeriodCollision.analyticColumn_binomial_product_bound a A
  have he := OAI.PiExponent.FinitePeriodCollision.analyticColumn_exponential_factor_bound h z hR hz
  have hp := OAI.PiExponent.FinitePeriodCollision.analyticColumn_power_factor_bound a A z hR hz
  have hmul1 := mul_le_mul hc he (norm_nonneg _) (Real.exp_nonneg _)
  have hmul2 := mul_le_mul hmul1 hp (norm_nonneg _)
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  rw [analyticColumn, norm_mul, norm_mul]
  calc
    ‖((↑(∏ i, (a i).choose (A i)) : ℂ))‖ * ‖Complex.exp ((h : ℂ) * z)‖ * ‖z ^ (∑ i, (a i - A i))‖
        ≤ Real.exp ((∑ i, (a i : ℝ)) * Real.log 2) *
          Real.exp ((h : ℝ) * R) *
          Real.exp ((∑ i, (a i : ℝ)) * Real.log R) := by
            exact hmul2
    _ = Real.exp ((h : ℝ) * R + (∑ i, (a i : ℝ)) * (Real.log 2 + Real.log R)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
    _ = Real.exp ((h : ℝ) * R + (∑ i, (a i : ℝ)) * Real.log (2 * R)) := by
          congr 1
          rw [Real.log_mul (by norm_num) (by linarith)]