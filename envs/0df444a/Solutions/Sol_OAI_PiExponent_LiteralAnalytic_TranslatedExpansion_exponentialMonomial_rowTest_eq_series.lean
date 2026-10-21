-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.exponentialMonomial_rowTest_eq_series
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:51:14.67348+00:00
-- url     : https://prove2.me/submissions/c12aa806-c669-4002-9981-e87ab7292887

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms

open scoped BigOperators Topology NNReal
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

/-!
# Analytic period series through a translated logarithm

This file develops, inside the `TranslatedExpansion` bundle, the power-series expansion of the
period function `t ↦ b * (1+t)^h * (center + log (1+t))^d` at the origin, and deduces the
coefficient-extraction formula for the Cauchy row test used by the translated expansion.
-/

namespace P2MTranslatedPort

theorem p2m_hasSum_coeff_C (b z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.C b) * z ^ n) b := by
  convert hasSum_ite_eq 0 b using 1
  funext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

theorem p2m_hasSum_coeff_X (z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ) * z ^ n) z := by
  convert hasSum_ite_eq 1 z using 1
  funext n
  by_cases hn : n = 1 <;> simp [PowerSeries.coeff_X, hn]

theorem p2m_hasSum_coeff_add {f g : PowerSeries ℂ} {x y z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x)
    (hg : HasSum (fun n => PowerSeries.coeff n g * z ^ n) y) :
    HasSum (fun n => PowerSeries.coeff n (f + g) * z ^ n) (x + y) := by
  simpa only [map_add, add_mul] using hf.add hg

theorem p2m_hasSum_coeff_one (z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (1 : PowerSeries ℂ) * z ^ n) 1 := by
  convert hasSum_ite_eq 0 (1 : ℂ) using 1
  funext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]

theorem p2m_hasSum_coeff_mul {f g : PowerSeries ℂ} {x y z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x)
    (hg : HasSum (fun n => PowerSeries.coeff n g * z ^ n) y) :
    HasSum (fun n => PowerSeries.coeff n (f * g) * z ^ n) (x * y) := by
  have hfn := hf.summable.norm
  have hgn := hg.summable.norm
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm.hasSum
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  rw [hf.tsum_eq, hg.tsum_eq] at heq
  rw [← heq] at hs
  rw [show (fun n => PowerSeries.coeff n (f * g) * z ^ n) =
      (fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        PowerSeries.coeff kl.1 f * z ^ kl.1 *
          (PowerSeries.coeff kl.2 g * z ^ kl.2)) by
    funext n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    have he : a.1 + a.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
    rw [← he, pow_add]
    ring]
  exact hs

theorem p2m_hasSum_coeff_pow {f : PowerSeries ℂ} {x z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x) (d : ℕ) :
    HasSum (fun n => PowerSeries.coeff n (f ^ d) * z ^ n) (x ^ d) := by
  induction d with
  | zero => simpa only [pow_zero] using p2m_hasSum_coeff_one z
  | succ d hd => simpa only [pow_succ] using p2m_hasSum_coeff_mul hd hf

theorem p2m_hasSum_formal_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.log ℂ) * z ^ n)
      (Complex.log (1 + z)) := by
  convert Complex.hasSum_taylorSeries_log hz using 1
  funext n
  by_cases hn : n = 0
  · simp [hn]
  · simp [PowerSeries.coeff_log, hn, map_div₀, map_pow]
    ring

/-- On the open unit disc, the period power series converges to the period function. -/
theorem p2m_hasSum_periodSeries (b center : ℂ) (h d : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n
        (PowerSeries.C b * (1 + PowerSeries.X) ^ h *
          (PowerSeries.C center + PowerSeries.log ℂ) ^ d) * z ^ n)
      (b * (1 + z) ^ h * (center + Complex.log (1 + z)) ^ d) := by
  exact p2m_hasSum_coeff_mul
    (p2m_hasSum_coeff_mul (p2m_hasSum_coeff_C b z)
      (p2m_hasSum_coeff_pow
        (p2m_hasSum_coeff_add (p2m_hasSum_coeff_one z) (p2m_hasSum_coeff_X z)) h))
    (p2m_hasSum_coeff_pow
      (p2m_hasSum_coeff_add (p2m_hasSum_coeff_C center z) (p2m_hasSum_formal_log hz)) d)

/-- The period function has at the origin the formal power series with coefficients given by the
period series. -/
theorem p2m_hasFPowerSeriesAt_periodFun (b center : ℂ) (h d : ℕ) :
    HasFPowerSeriesAt
      (fun t : ℂ => b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d)
      (FormalMultilinearSeries.ofScalars ℂ (fun n =>
        PowerSeries.coeff n
          (PowerSeries.C b * (1 + PowerSeries.X) ^ h *
            (PowerSeries.C center + PowerSeries.log ℂ) ^ d))) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hn : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul, mul_comm] using
    p2m_hasSum_periodSeries b center h d hn

theorem p2m_analyticAt_periodFun (b center : ℂ) (h d : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (fun t : ℂ => b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d) z := by
  apply AnalyticAt.mul
  · fun_prop
  · exact (analyticAt_const.add ((analyticAt_const.add analyticAt_id).clog
      (Complex.mem_slitPlane_of_norm_lt_one hz))).pow d

/-- The Cauchy row test of the period function extracts the corresponding coefficient. -/
theorem p2m_rowTest_periodFun_eq_coeff (b center : ℂ) (h d ell : ℕ) :
    rowTest ell (fun t : ℂ => b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d) =
      PowerSeries.coeff ell
        (PowerSeries.C b * (1 + PowerSeries.X) ^ h *
          (PowerSeries.C center + PowerSeries.log ℂ) ^ d) := by
  have hd : DifferentiableOn ℂ
      (fun t : ℂ => b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d)
      (Metric.closedBall 0 (1 / 2)) := by
    intro z hz
    have hz' : ‖z‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact (p2m_analyticAt_periodFun b center h d (by linarith : ‖z‖ < 1)).differentiableAt
      |>.differentiableWithinAt
  have hball := hd.hasFPowerSeriesOnBall (R := (1 / 2 : NNReal)) (by norm_num)
  have heq := hball.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (p2m_hasFPowerSeriesAt_periodFun b center h d)
  have hh := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p ell (fun _ => 1)) heq
  simpa only [rowTest, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul, FormalMultilinearSeries.coeff_ofScalars,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh

/-- The Cauchy row test only depends on the values on the circle of radius `1/2`. -/
theorem p2m_rowTest_congr_sphere {f g : ℂ → ℂ} (ell : ℕ)
    (hfg : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2), f z = g z) :
    rowTest ell f = rowTest ell g := by
  simp only [rowTest, cauchyPowerSeries_apply]
  congr 1
  apply circleIntegral.integral_congr (by norm_num)
  intro z hz
  change (1 / (z - 0)) ^ ell • (z - 0)⁻¹ • f z =
    (1 / (z - 0)) ^ ell • (z - 0)⁻¹ • g z
  rw [hfg z hz]

end P2MTranslatedPort

/-- On the circle of radius `1/2`, the translated exponential monomial equals the period
function with centre `j * period`. -/
theorem p2m_exponentialMonomial_eq_periodFun_on_sphere (b : ℂ) (j h d : ℕ) :
    ∀ t ∈ Metric.sphere (0 : ℂ) (1 / 2),
      exponentialMonomial b (h : ℂ) d
          (((j : ℂ) * period) + Complex.log (1 + t)) =
        b * (1 + t) ^ h *
          (((j : ℂ) * period) + Complex.log (1 + t)) ^ d := by
  intro t ht
  have hn : ‖t‖ = (1 / 2 : ℝ) := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ht
  have hz0 : 1 + t ≠ 0 := by
    intro heq
    have hneg : t = -1 := by linear_combination heq
    rw [hneg] at hn
    norm_num at hn
  have hper : Complex.exp ((j : ℂ) * period) = 1 := by
    have hc' : (j : ℂ) * period = (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [period]
      ring
    rw [hc', Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
  have hexp : Complex.exp
      ((h : ℂ) * (((j : ℂ) * period) + Complex.log (1 + t))) = (1 + t) ^ h := by
    rw [Complex.exp_nat_mul, Complex.exp_add, hper, one_mul, Complex.exp_log hz0]
  unfold exponentialMonomial
  rw [hexp]

theorem solution (b : ℂ) (j h d ell : ℕ) :
    rowTest ell (fun t => exponentialMonomial b (h : ℂ) d
      ((j : ℂ) * period + Complex.log (1 + t))) =
    PowerSeries.coeff ell
      (PowerSeries.C b * (1 + PowerSeries.X) ^ h *
        (PowerSeries.C ((j : ℂ) * period) + PowerSeries.log ℂ) ^ d) := by
  rw [P2MTranslatedPort.p2m_rowTest_congr_sphere ell
    (p2m_exponentialMonomial_eq_periodFun_on_sphere b j h d)]
  exact P2MTranslatedPort.p2m_rowTest_periodFun_eq_coeff b ((j : ℂ) * period) h d ell
