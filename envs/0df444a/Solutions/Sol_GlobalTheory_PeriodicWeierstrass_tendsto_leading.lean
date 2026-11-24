-- Prove2me | solution 1 for GlobalTheory.PeriodicWeierstrass.tendsto_leading
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:33.752109+00:00
-- url     : https://prove2.me/submissions/b9ad5ae5-3dea-4147-8374-89a3a3ca8ebf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsConstOfSqMulTendstoZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology
noncomputable section
open GlobalTheory
open GlobalTheory.PeriodicWeierstrass
variable (L : PeriodPair)
open Filter PeriodPair
open scoped Topology
namespace GlobalTheory.PeriodicWeierstrass
namespace _root_.GlobalTheory.PeriodicWeierstrass
theorem _root_.solution (W : WeierstrassCurve ℂ)
    {x y t : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hE : ∀ᶠ z in 𝓝[≠] 0, W.toAffine.Equation (x z) (y z))
    (ht : AnalyticAt ℂ t 0) (ht0 : t 0 = 0) (ht1 : deriv t 0 = c)
    (hty : ∀ᶠ z in 𝓝[≠] 0, t z * y z = -x z)
    (hy : Tendsto (fun z ↦ ‖y z‖) (𝓝[≠] 0) atTop) :
    Tendsto (fun z ↦ z ^ 2 * (c ^ 2 * x z)) (𝓝[≠] 0) (𝓝 1) ∧
      Tendsto (fun z ↦ z ^ 3 * (c ^ 3 * y z)) (𝓝[≠] 0) (𝓝 (-1)) := by
  have hu : Tendsto (fun z => z⁻¹ * t z) (𝓝[≠] 0) (𝓝 c) := by
    have := ht.differentiableAt.hasDerivAt.tendsto_slope_zero
    rw [ht1] at this
    simpa [ht0] using this
  have hv : Tendsto (fun z => c / (z⁻¹ * t z)) (𝓝[≠] 0) (𝓝 1) := by
    have := (tendsto_const_nhds (x := c)).div hu hc
    rw [div_self hc] at this
    exact this
  have htz0 : ∀ᶠ z in 𝓝[≠] 0, t z ≠ 0 :=
    (hu.eventually_ne hc).mono fun z hz => right_ne_zero_of_mul hz
  have ht' : Tendsto t (𝓝[≠] 0) (𝓝 0) := by
    have := ht.continuousAt.tendsto
    rw [ht0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun z => (y z)⁻¹) (𝓝[≠] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv]
    exact tendsto_inv_atTop_zero.comp hy
  have hy0 : ∀ᶠ z in 𝓝[≠] 0, y z ≠ 0 :=
    (hy.eventually_gt_atTop 0).mono fun z hz => norm_pos_iff.mp hz
  have hP := ((by fun_prop : Continuous fun p : ℂ × ℂ => -(1 - W.a₁ * p.1 + W.a₃ * p.2
      - W.a₂ * p.1 ^ 2 + W.a₄ * p.1 * p.2 - W.a₆ * p.2 ^ 2)).tendsto (0, 0)).comp
    (ht'.prodMk_nhds hs)
  have hT : Tendsto (fun z => t z ^ 3 * y z) (𝓝[≠] 0) (𝓝 (-1)) := by
    have hP' : Tendsto (fun z => -(1 - W.a₁ * t z + W.a₃ * (y z)⁻¹ - W.a₂ * t z ^ 2
        + W.a₄ * t z * (y z)⁻¹ - W.a₆ * ((y z)⁻¹) ^ 2)) (𝓝[≠] 0) (𝓝 (-1)) := by
      convert hP using 2 <;> simp
    refine hP'.congr' ?_
    filter_upwards [hE, hty, hy0] with z hEz htz hyz
    rw [WeierstrassCurve.Affine.equation_iff] at hEz
    have hx : x z = -(t z * y z) := by linear_combination htz
    rw [hx] at hEz
    field_simp
    linear_combination -hEz
  constructor
  · have h1 : Tendsto (fun z => -((c / (z⁻¹ * t z)) ^ 2 * (t z ^ 3 * y z))) (𝓝[≠] 0)
        (𝓝 1) := by simpa using ((hv.pow 2).mul hT).neg
    refine h1.congr' ?_
    filter_upwards [hty, htz0, self_mem_nhdsWithin] with z htz hz0 (hz : z ≠ 0)
    have hx : x z = -(t z * y z) := by linear_combination htz
    rw [hx]
    field_simp
  · have h1 : Tendsto (fun z => (c / (z⁻¹ * t z)) ^ 3 * (t z ^ 3 * y z)) (𝓝[≠] 0)
        (𝓝 (-1)) := by simpa using (hv.pow 3).mul hT
    refine h1.congr' ?_
    filter_upwards [htz0, self_mem_nhdsWithin] with z hz0 (hz : z ≠ 0)
    field_simp
end _root_.GlobalTheory.PeriodicWeierstrass
end GlobalTheory.PeriodicWeierstrass
