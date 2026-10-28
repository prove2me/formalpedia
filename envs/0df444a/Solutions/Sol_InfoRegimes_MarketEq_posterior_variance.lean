-- Prove2me | solution 1 for InfoRegimes.MarketEq.posterior_variance
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:39:22.203234+00:00
-- url     : https://prove2.me/submissions/655b7347-e1f6-4744-9293-b4b1319d50f9

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m X : Ω → ℝ) (hm : MemLp m 2 μ) (hX : MemLp X 2 μ)
    (hind : IndepFun m X μ) (b c : ℝ)
    (hden : 0 < b ^ 2 * variance m μ + c ^ 2 * variance X μ) :
    let Pr : Ω → ℝ := fun ω => b * m ω - c * X ω
    let K : ℝ := covariance m Pr μ / variance Pr μ
    K = b * variance m μ / (b ^ 2 * variance m μ + c ^ 2 * variance X μ) ∧
      variance (fun ω => m ω - K * Pr ω) μ = (1 - K * b) * variance m μ := by
  intro Pr K
  have hbm : MemLp (fun ω => b * m ω) 2 μ := hm.const_mul b
  have hcX : MemLp (fun ω => c * X ω) 2 μ := hX.const_mul c
  have hPr : MemLp Pr 2 μ := hbm.sub hcX
  have hcovmX : covariance m X μ = 0 := hind.covariance_eq_zero hm hX
  have hcov : covariance m Pr μ = b * variance m μ := by
    show covariance m (fun ω => b * m ω - c * X ω) μ = _
    rw [covariance_fun_sub_right hm hbm hcX, covariance_const_mul_right,
      covariance_const_mul_right, covariance_self hm.aemeasurable, hcovmX]
    ring
  have hvar : variance Pr μ = b ^ 2 * variance m μ + c ^ 2 * variance X μ := by
    show variance (fun ω => b * m ω - c * X ω) μ = _
    rw [variance_fun_sub hbm hcX, variance_const_mul, variance_const_mul,
      covariance_const_mul_left, covariance_const_mul_right, hcovmX]
    ring
  have hK : K = b * variance m μ / (b ^ 2 * variance m μ + c ^ 2 * variance X μ) := by
    show covariance m Pr μ / variance Pr μ = _
    rw [hcov, hvar]
  refine ⟨hK, ?_⟩
  have hKD : K * (b ^ 2 * variance m μ + c ^ 2 * variance X μ) = b * variance m μ := by
    rw [hK]; field_simp
  rw [variance_fun_sub hm (hPr.const_mul K), covariance_const_mul_right, variance_const_mul,
    hcov, hvar]
  linear_combination K * hKD
