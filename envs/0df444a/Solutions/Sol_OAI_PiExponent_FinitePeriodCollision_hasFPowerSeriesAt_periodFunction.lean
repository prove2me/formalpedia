-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.hasFPowerSeriesAt_periodFunction
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:35:15.50688+00:00
-- url     : https://prove2.me/submissions/aab02139-bc31-4dbc-91d0-2a800158f372

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open scoped BigOperators
open Filter Topology

namespace P2MPeriodPort

/-- The coefficients of the formal logarithm are the Taylor coefficients of `log (1 + z)`:
`coeff n (log ℂ) = -(-1)^n/n`. -/
theorem p2m_coeff_log (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.log ℂ) = -(-1 : ℂ) ^ n / n := by
  rw [PowerSeries.coeff_log]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, map_div₀, map_pow]
    rw [pow_succ]
    simp

/-- The formal logarithm evaluates at `z` near the origin to `log (1 + z)`. -/
theorem p2m_hasSum_formal_log_eventually :
    ∀ᶠ z : ℂ in 𝓝 0,
      HasSum (fun n => PowerSeries.coeff n (PowerSeries.log ℂ) * z ^ n)
        (Complex.log (1 + z)) := by
  have h := hasFPowerSeriesAt_clog_one_add
  rw [hasFPowerSeriesAt_iff] at h
  filter_upwards [h] with z hz
  simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, p2m_coeff_log,
    zero_add, mul_comm] using hz

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
      (fun n => ∑ kl ∈ Finset.antidiagonal n,
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

/-- Near the origin, the period series evaluates to the period function. -/
theorem p2m_hasSum_period_eventually (b center : ℂ) (h d : ℕ) :
    ∀ᶠ z : ℂ in 𝓝 0,
      HasSum (fun n => PowerSeries.coeff n
          (PowerSeries.C b * (1 + PowerSeries.X) ^ h *
            (PowerSeries.C center + PowerSeries.log ℂ) ^ d) * z ^ n)
        (b * (1 + z) ^ h * (center + Complex.log (1 + z)) ^ d) := by
  filter_upwards [p2m_hasSum_formal_log_eventually] with z hz
  exact p2m_hasSum_coeff_mul
    (p2m_hasSum_coeff_mul (p2m_hasSum_coeff_C b z)
      (p2m_hasSum_coeff_pow
        (p2m_hasSum_coeff_add (p2m_hasSum_coeff_one z) (p2m_hasSum_coeff_X z)) h))
    (p2m_hasSum_coeff_pow (p2m_hasSum_coeff_add (p2m_hasSum_coeff_C center z) hz) d)

end P2MPeriodPort

theorem solution (b center : ℂ) (h d : ℕ) :
    HasFPowerSeriesAt
      (fun t : ℂ => b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d)
      (FormalMultilinearSeries.ofScalars ℂ (fun n =>
        PowerSeries.coeff n
          (PowerSeries.C b * (1 + PowerSeries.X) ^ h *
            (PowerSeries.C center + PowerSeries.log ℂ) ^ d))) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [P2MPeriodPort.p2m_hasSum_period_eventually b center h d] with z hz
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul, mul_comm] using hz
