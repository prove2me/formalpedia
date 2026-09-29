-- Prove2me | solution 1 for MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2cd55b6e-dd4e-5785-964b-8984d976ea91

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le

set_option autoImplicit false

open MeasureTheory Metric Filter Topology

namespace RS11IC

theorem main {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {U : Set ℂ} (hU : IsOpen U) (F : ℂ → Y → ℂ)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) ν)
    (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U)
    (hdom : ∀ z₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M ν ∧
      ∀ z ∈ Metric.ball z₀ ε, ∀ a : Y, ‖F z a‖ ≤ M a) :
    DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U := by
  intro z₀ hz₀
  obtain ⟨ε, hε, M, hM, hbd⟩ := hdom z₀ hz₀
  obtain ⟨δ₀, hδ₀, hballU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set δ : ℝ := min ε δ₀ / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have h2δε : 2 * δ ≤ ε := by rw [hδdef]; linarith [min_le_left ε δ₀]
  have h2δ₀ : 2 * δ ≤ δ₀ := by rw [hδdef]; linarith [min_le_right ε δ₀]
  have hBU : ball z₀ (2 * δ) ⊆ U := (ball_subset_ball h2δ₀).trans hballU
  have hBε : ball z₀ (2 * δ) ⊆ ball z₀ ε := ball_subset_ball h2δε

  set F' : ℂ → Y → ℂ := fun z a => deriv (fun w => F w a) z with hF'
  have hderiv : ∀ a : Y, ∀ z ∈ ball z₀ δ, HasDerivAt (fun w => F w a) (F' z a) z := by
    intro a z hz
    have hzU : z ∈ U := hBU (ball_subset_ball (by linarith) hz)
    exact ((hhol a).differentiableAt (hU.mem_nhds hzU)).hasDerivAt

  have hsub : ∀ z ∈ ball z₀ δ, closedBall z δ ⊆ ball z₀ (2 * δ) := by
    intro z hz w hw
    rw [mem_ball] at hz ⊢
    rw [mem_closedBall] at hw
    calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < δ + δ := by linarith
      _ = 2 * δ := by ring
  have hbound : ∀ a : Y, ∀ z ∈ ball z₀ δ, ‖F' z a‖ ≤ M a / δ := by
    intro a z hz
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ ?_ ?_
    · have hcl : closure (ball z δ) ⊆ U :=
        closure_ball_subset_closedBall.trans ((hsub z hz).trans hBU)
      exact ((hhol a).mono hcl).diffContOnCl
    · intro w hw
      exact hbd w (hBε (hsub z hz (sphere_subset_closedBall hw))) a

  have hF'meas : AEStronglyMeasurable (F' z₀) ν := by
    set t : ℕ → ℂ := fun n => ((δ / ((n : ℝ) + 2) : ℝ) : ℂ) with ht
    have htpos : ∀ n : ℕ, 0 < δ / ((n : ℝ) + 2) := fun n => by positivity
    have ht_ne : ∀ n : ℕ, t n ≠ 0 := fun n => by
      show (((δ / ((n : ℝ) + 2) : ℝ)) : ℂ) ≠ 0
      exact_mod_cast (htpos n).ne'
    have ht_lt : ∀ n : ℕ, ‖t n‖ < δ := fun n => by
      show ‖((((δ / ((n : ℝ) + 2) : ℝ)) : ℂ))‖ < δ
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (htpos n), div_lt_iff₀ (by positivity)]
      nlinarith [hδ]
    have ht_mem : ∀ n : ℕ, z₀ + t n ∈ U := fun n =>
      hBU (by rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; linarith [ht_lt n])
    have ht0 : Tendsto t atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        apply Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      rw [Complex.ofReal_zero] at h2
      exact h2
    have ht0' : Tendsto t atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨ht0, Eventually.of_forall fun n => ht_ne n⟩
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n a => (t n)⁻¹ • (F (z₀ + t n) a - F z₀ a)) (fun n => ?_) ?_
    · show AEStronglyMeasurable (fun a => (t n)⁻¹ • (F (z₀ + t n) a - F z₀ a)) ν
      exact ((hmeas _ (ht_mem n)).sub (hmeas z₀ hz₀)).const_smul ((t n)⁻¹)
    · refine Eventually.of_forall fun a => ?_
      have h := (hderiv a z₀ (mem_ball_self hδ)).tendsto_slope_zero
      exact h.comp ht0'

  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (F := F) (F' := F') (x₀ := z₀)
    (bound := fun a => M a / δ) (ball_mem_nhds z₀ hδ)
    (Filter.eventually_of_mem (hU.mem_nhds hz₀) hmeas)
    (Integrable.mono' hM (hmeas z₀ hz₀) (Eventually.of_forall fun a => hbd z₀ (mem_ball_self hε) a))
    hF'meas
    (Eventually.of_forall fun a z hz => hbound a z hz)
    (hM.div_const δ)
    (Eventually.of_forall fun a z hz => hderiv a z hz)
  exact key.2.differentiableAt.differentiableWithinAt

end RS11IC

theorem solution
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {U : Set ℂ} (hU : IsOpen U) (F : ℂ → Y → ℂ)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) ν)
    (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U)
    (hdom : ∀ z₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M ν ∧
      ∀ z ∈ Metric.ball z₀ ε, ∀ a : Y, ‖F z a‖ ≤ M a) :
    DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U :=
  RS11IC.main ν hU F hmeas hhol hdom

end S_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
end P2MW
export P2MW.S_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le (solution)
