-- Prove2me | solution 1 for MarkovChainCLT.abs_exp_variance_sub_le_of_tendstoInDistribution
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T01:07:58.387632+00:00
-- url     : https://prove2.me/submissions/fd7af3e7-ab49-4039-acb7-76f49cb8e788

import Theorems.Thm_ProbabilityTheory_integral_cos_gaussianReal
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y Z : ℕ → Ω → ℝ) (v w : ℝ≥0) (ε : ℝ)
    (hY : ∀ n, Measurable (Y n)) (hZ : ∀ n, Measurable (Z n))
    (hcY : TendstoInDistribution Y atTop (id : ℝ → ℝ) (fun _ => μ) (gaussianReal 0 v))
    (hcZ : TendstoInDistribution Z atTop (id : ℝ → ℝ) (fun _ => μ) (gaussianReal 0 w))
    (hint : ∀ n, Integrable (fun ω => |Y n ω - Z n ω|) μ)
    (hdiff : ∀ n, ∫ ω, |Y n ω - Z n ω| ∂μ ≤ ε) :
    |Real.exp (-(v : ℝ) / 2) - Real.exp (-(w : ℝ) / 2)| ≤ ε := by
  classical
  -- `cos` as a bounded continuous function
  set F : BoundedContinuousFunction ℝ ℝ :=
    ⟨⟨Real.cos, Real.continuous_cos⟩, ⟨2, fun x y => by
      rw [Real.dist_eq]
      have h1 : |Real.cos x| ≤ 1 := Real.abs_cos_le_one x
      have h2 : |Real.cos y| ≤ 1 := Real.abs_cos_le_one y
      calc |Real.cos x - Real.cos y| ≤ |Real.cos x| + |Real.cos y| := abs_sub _ _
        _ ≤ 2 := by linarith⟩⟩ with hF
  have hFapp : ∀ x : ℝ, F x = Real.cos x := fun x => rfl
  -- transfer of the weak limit to the integral of `cos`
  have main : ∀ (W : ℕ → Ω → ℝ) (u : ℝ≥0), (∀ n, Measurable (W n)) →
      TendstoInDistribution W atTop (id : ℝ → ℝ) (fun _ => μ) (gaussianReal 0 u) →
      Tendsto (fun n => ∫ ω, Real.cos (W n ω) ∂μ) atTop (𝓝 (Real.exp (-(u : ℝ) / 2))) := by
    intro W u hW hc
    have htend := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hc.tendsto F
    simp only [ProbabilityMeasure.coe_mk] at htend
    have hmapn : ∀ n : ℕ, ∫ x, F x ∂(μ.map (W n)) = ∫ ω, Real.cos (W n ω) ∂μ := by
      intro n
      rw [integral_map (hW n).aemeasurable F.continuous.aestronglyMeasurable]
      rfl
    have hmapl : ∫ x, F x ∂((gaussianReal 0 u).map (id : ℝ → ℝ))
        = Real.exp (-(u : ℝ) / 2) := by
      rw [integral_map measurable_id.aemeasurable F.continuous.aestronglyMeasurable]
      exact ProbabilityTheory.integral_cos_gaussianReal u
    simp only [hmapn, hmapl] at htend
    exact htend
  have hMY := main Y v hY hcY
  have hMZ := main Z w hZ hcZ
  -- the two integrals stay within `ε` of one another
  have hcosint : ∀ (W : ℕ → Ω → ℝ) (n : ℕ), Measurable (W n) →
      Integrable (fun ω => Real.cos (W n ω)) μ := by
    intro W n hW
    exact ⟨(Real.continuous_cos.measurable.comp hW).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1)
        (ae_of_all _ (fun ω => by simpa using Real.abs_cos_le_one (W n ω)))⟩
  have hstep : ∀ n, |(∫ ω, Real.cos (Y n ω) ∂μ) - ∫ ω, Real.cos (Z n ω) ∂μ| ≤ ε := by
    intro n
    have hiY := hcosint Y n (hY n)
    have hiZ := hcosint Z n (hZ n)
    have hsub : (∫ ω, Real.cos (Y n ω) ∂μ) - ∫ ω, Real.cos (Z n ω) ∂μ
        = ∫ ω, (Real.cos (Y n ω) - Real.cos (Z n ω)) ∂μ := (integral_sub hiY hiZ).symm
    rw [hsub]
    have hbound : ∀ ω, |Real.cos (Y n ω) - Real.cos (Z n ω)| ≤ |Y n ω - Z n ω| := by
      intro ω
      have := Real.lipschitzWith_cos.dist_le_mul (Y n ω) (Z n ω)
      rw [Real.dist_eq, Real.dist_eq] at this
      simpa using this
    have habs : |∫ ω, (Real.cos (Y n ω) - Real.cos (Z n ω)) ∂μ|
        ≤ ∫ ω, |Real.cos (Y n ω) - Real.cos (Z n ω)| ∂μ :=
      abs_integral_le_integral_abs
    have habsint : Integrable (fun ω => |Real.cos (Y n ω) - Real.cos (Z n ω)|) μ :=
      (hiY.sub hiZ).abs
    have hmono : ∫ ω, |Real.cos (Y n ω) - Real.cos (Z n ω)| ∂μ
        ≤ ∫ ω, |Y n ω - Z n ω| ∂μ :=
      integral_mono habsint (hint n) hbound
    calc |∫ ω, (Real.cos (Y n ω) - Real.cos (Z n ω)) ∂μ|
        ≤ ∫ ω, |Real.cos (Y n ω) - Real.cos (Z n ω)| ∂μ := habs
      _ ≤ ∫ ω, |Y n ω - Z n ω| ∂μ := hmono
      _ ≤ ε := hdiff n
  -- pass to the limit
  have hlim : Tendsto
      (fun n => |(∫ ω, Real.cos (Y n ω) ∂μ) - ∫ ω, Real.cos (Z n ω) ∂μ|) atTop
      (𝓝 |Real.exp (-(v : ℝ) / 2) - Real.exp (-(w : ℝ) / 2)|) :=
    ((hMY.sub hMZ).abs)
  exact le_of_tendsto hlim (Eventually.of_forall hstep)
