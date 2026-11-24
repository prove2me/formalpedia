-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.tubeShift_differentiableOn_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:15.305065+00:00
-- url     : https://prove2.me/submissions/cd0b6024-530c-4ebb-886c-f46394a23995

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftTubeDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (U : Set ℂ) (hU : IsOpen U) (F : ℂ → α → ℂ)
    (hol : ∀ y, DifferentiableOn ℂ (fun w => F w y) U)
    (meas : ∀ w ∈ U, AEStronglyMeasurable (F w) μ)
    (dom : ∀ w₀ ∈ U, ∀ ρ : ℝ, 0 < ρ → Metric.closedBall w₀ ρ ⊆ U →
      ∃ g : α → ℝ, Integrable g μ ∧ ∀ w ∈ Metric.closedBall w₀ ρ, ∀ y, ‖F w y‖ ≤ g y) :
    DifferentiableOn ℂ (fun w => ∫ y, F w y ∂μ) U := by
  intro w₀ hw₀
  obtain ⟨ρ', hρ', hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hw₀)
  obtain ⟨g, hg, hgb⟩ := dom w₀ hw₀ ρ' hρ' hb
  have hρ : 0 < ρ' / 2 := by positivity
  have hball : Metric.ball w₀ (ρ' / 2) ⊆ U := fun w hw =>
    hb (Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hw))
  have hderiv : ∀ w ∈ U, ∀ y, HasDerivAt (fun w => F w y) (deriv (fun w => F w y) w) w :=
    fun w hw y => ((hol y).differentiableAt (hU.mem_nhds hw)).hasDerivAt
  have hseq : Tendsto (fun n : ℕ => (ρ' / 2 : ℝ) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ρ' / 2)
  have hpos : ∀ n : ℕ, 0 < (ρ' / 2 : ℝ) * (1 / ((n : ℝ) + 1)) := fun n => by positivity
  let u : ℕ → ℂ := fun n => w₀ + (((ρ' / 2 : ℝ) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)
  have hu : ∀ n, u n ∈ U := fun n => by
    apply hb
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [u, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos n)]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith
  have hmeas' : AEStronglyMeasurable (fun y => deriv (fun w => F w y) w₀) μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (n : ℕ) y => slope (fun w => F w y) w₀ (u n)) (fun n => ?_)
      (ae_of_all _ fun y => ?_)
    · simp only [slope, vsub_eq_sub]
      exact ((meas _ (hu n)).sub (meas _ hw₀)).const_smul (u n - w₀)⁻¹
    · refine (hasDerivAt_iff_tendsto_slope.1 (hderiv w₀ hw₀ y)).comp
        (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩)
      · have := ((Complex.continuous_ofReal.tendsto 0).comp hseq).const_add w₀
        simpa [u] using this
      · have : (((ρ' / 2 : ℝ) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (hpos n).ne'
        simpa [u] using this
  have hint : Integrable (F w₀) μ := by
    refine hg.mono' (meas w₀ hw₀) (ae_of_all _ fun y => ?_)
    exact hgb w₀ (Metric.mem_closedBall_self hρ'.le) y
  have hbound : ∀ᵐ y ∂μ, ∀ w ∈ Metric.ball w₀ (ρ' / 2),
      ‖deriv (fun w => F w y) w‖ ≤ g y / (ρ' / 2) := by
    refine ae_of_all _ fun y w hw => ?_
    have hsub : Metric.closedBall w (ρ' / 2) ⊆ Metric.closedBall w₀ ρ' := by
      intro z hz
      rw [Metric.mem_closedBall] at hz ⊢
      have := Metric.mem_ball.1 hw
      linarith [dist_triangle z w w₀]
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
      ((hol y).diffContOnCl_ball (hsub.trans hb))
      (fun z hz => hgb z (hsub (Metric.sphere_subset_closedBall hz)) y)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℂ) (F := F)
    (F' := fun w y => deriv (fun w => F w y) w) (x₀ := w₀) (s := Metric.ball w₀ (ρ' / 2))
    (bound := fun y => g y / (ρ' / 2)) (Metric.ball_mem_nhds _ hρ)
    (Filter.eventually_of_mem (hU.mem_nhds hw₀) meas) hint hmeas' hbound (hg.div_const _)
    (ae_of_all _ fun y w hw => hderiv w (hball hw) y)
  exact key.2.differentiableAt.differentiableWithinAt
end GlobalTheory.CompanionTheory.EisTube
