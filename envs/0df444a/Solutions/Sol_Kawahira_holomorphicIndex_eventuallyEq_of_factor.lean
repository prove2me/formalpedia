-- Prove2me | solution 1 for Kawahira.holomorphicIndex_eventuallyEq_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:07:28.574837+00:00
-- url     : https://prove2.me/submissions/2d0ba6c6-aec4-4348-8351-4867d64f8ff9

import Definitions.Def_Kawahira_zeta

open Complex Topology Filter Metric Set

namespace Kawahira

theorem holomorphicIndexEventuallyEqOfFactorProof (g q : ℂ → ℂ) (a : ℂ)
    (hq : AnalyticAt ℂ q a) (hqa : q a ≠ 0)
    (hfactor : (fun z => z - g z) =ᶠ[𝓝 a] fun z => (z - a) * q z) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), holomorphicIndex g a r = (q a)⁻¹ := by
  have hgood : {z : ℂ | AnalyticAt ℂ q z ∧ q z ≠ 0 ∧ z - g z = (z - a) * q z} ∈ 𝓝 a := by
    filter_upwards [hq.eventually_analyticAt, hq.continuousAt.eventually_ne hqa,
      hfactor] with z hz hne hfac
    exact ⟨hz, hne, hfac⟩
  have hballs : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall a r ⊆
      {z : ℂ | AnalyticAt ℂ q z ∧ q z ≠ 0 ∧ z - g z = (z - a) * q z} :=
    (eventually_closedBall_subset hgood).filter_mono nhdsWithin_le_nhds
  filter_upwards [hballs, self_mem_nhdsWithin] with r hr hrpos
  have hr0 : 0 < r := hrpos
  have hd : DifferentiableOn ℂ (fun z => (q z)⁻¹) (closedBall a r) := by
    intro z hz
    exact ((hr hz).1.differentiableAt.inv (hr hz).2.1).differentiableWithinAt
  have hint : (∮ z in C(a, r), (z - g z)⁻¹) =
      2 * Real.pi * Complex.I * (q a)⁻¹ := by
    calc
      (∮ z in C(a, r), (z - g z)⁻¹) =
          ∮ z in C(a, r), (z - a)⁻¹ • (q z)⁻¹ := by
        apply circleIntegral.integral_congr hr0.le
        intro z hz
        change (z - g z)⁻¹ = (z - a)⁻¹ * (q z)⁻¹
        rw [(hr (sphere_subset_closedBall hz)).2.2, mul_inv]
      _ = 2 * Real.pi * Complex.I * (q a)⁻¹ := by
        simpa only [smul_eq_mul] using
          hd.circleIntegral_sub_inv_smul (show a ∈ ball a r by simpa using hr0)
  rw [holomorphicIndex, hint]
  field_simp

end Kawahira

theorem solution (g q : ℂ → ℂ) (a : ℂ)
    (hq : AnalyticAt ℂ q a) (hqa : q a ≠ 0)
    (hfactor : (fun z => z - g z) =ᶠ[𝓝 a] fun z => (z - a) * q z) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), Kawahira.holomorphicIndex g a r = (q a)⁻¹ := by
  exact Kawahira.holomorphicIndexEventuallyEqOfFactorProof g q a hq hqa hfactor
