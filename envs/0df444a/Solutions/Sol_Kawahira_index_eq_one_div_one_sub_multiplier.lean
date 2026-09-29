-- Prove2me | solution 1 for Kawahira.index_eq_one_div_one_sub_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T21:56:18.189972+00:00
-- url     : https://prove2.me/submissions/0947eec4-050b-4171-9bad-8d7b54e84160

import Definitions.Def_Kawahira_zeta

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace KawLoc2

open Complex Topology Kawahira Metric

theorem index_eq_one_div_one_sub_multiplier (g : ℂ → ℂ) (a : ℂ)
    (hg : AnalyticAt ℂ g a) (hfix : g a = a) (hlam : deriv g a ≠ 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), holomorphicIndex g a r = 1 / (1 - deriv g a) := by
  -- the displacement `φ z = z - g z` has a simple zero at `a`
  have hφa : AnalyticAt ℂ (fun z : ℂ => z - g z) a := analyticAt_id.sub hg
  have hφ0 : (fun z : ℂ => z - g z) a = 0 := by simp [hfix]
  have hφ' : deriv (fun z : ℂ => z - g z) a = 1 - deriv g a := by
    have h1 : HasDerivAt (fun z : ℂ => z - g z) (1 - deriv g a) a := by
      simpa using (hasDerivAt_id a).fun_sub hg.differentiableAt.hasDerivAt
    exact h1.deriv
  set k : ℂ → ℂ := dslope (fun z : ℂ => z - g z) a with hk
  have hka : k a = 1 - deriv g a := by rw [hk, dslope_same, hφ']
  have hka0 : k a ≠ 0 := by rw [hka]; exact sub_ne_zero.2 (Ne.symm hlam)
  have hkan : AnalyticAt ℂ k a := by
    obtain ⟨p, hp⟩ := hφa
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have hfac : ∀ z : ℂ, (z - a) * k z = z - g z := by
    intro z
    have h := sub_smul_dslope (fun z : ℂ => z - g z) a z
    simp only [hfix, sub_self, sub_zero, smul_eq_mul] at h
    simpa [hk] using h
  -- `k` is analytic and nonvanishing on a small ball
  have hnear : ∀ᶠ z in 𝓝 a, AnalyticAt ℂ k z ∧ k z ≠ 0 := by
    filter_upwards [hkan.eventually_analyticAt,
      hkan.continuousAt.eventually_ne hka0] with z h1 h2
    exact ⟨h1, h2⟩
  rw [Metric.eventually_nhds_iff] at hnear
  obtain ⟨R, hR, hball⟩ := hnear
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  obtain ⟨hr0, hrR⟩ := hr
  have hsub : closedBall a r ⊆ ball a R := fun z hz => by
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  have hinv : ContinuousOn (fun z => (k z)⁻¹) (closedBall a r) := by
    intro z hz
    have hz' := hball (by simpa [dist_comm] using hsub hz)
    exact ((hz'.1.continuousAt.inv₀ hz'.2).continuousWithinAt)
  have hdiff : ∀ z ∈ ball a r \ (∅ : Set ℂ), DifferentiableAt ℂ (fun z => (k z)⁻¹) z := by
    intro z hz
    have hz' := hball (by
      simpa [dist_comm] using hsub (ball_subset_closedBall hz.1))
    exact hz'.1.differentiableAt.inv hz'.2
  have hcauchy : (∮ z in C(a, r), (z - a)⁻¹ • (k z)⁻¹) = (2 * Real.pi * Complex.I) • (k a)⁻¹ :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
      hr0 Set.countable_empty hinv hdiff
  have hcongr : (∮ z in C(a, r), (z - g z)⁻¹) = ∮ z in C(a, r), (z - a)⁻¹ • (k z)⁻¹ := by
    refine circleIntegral.integral_congr hr0.le ?_
    intro z hz
    rw [mem_sphere, Complex.dist_eq] at hz
    have hza : z - a ≠ 0 := by
      intro hc
      rw [hc] at hz
      simp at hz
      linarith
    show (z - g z)⁻¹ = (z - a)⁻¹ • (k z)⁻¹
    rw [← hfac z, mul_inv, smul_eq_mul]
  rw [holomorphicIndex, hcongr, hcauchy, smul_eq_mul, hka]
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp

end KawLoc2

open Complex Topology Kawahira in
theorem solution (g : ℂ → ℂ) (a : ℂ)
    (hg : AnalyticAt ℂ g a) (hfix : g a = a) (hlam : deriv g a ≠ 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), holomorphicIndex g a r = 1 / (1 - deriv g a) :=
  KawLoc2.index_eq_one_div_one_sub_multiplier g a hg hfix hlam
