-- Prove2me | solution 1 for MeasureTheory.integral_directional_derivative_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T12:14:25.984517+00:00
-- url     : https://prove2.me/submissions/17257426-121d-4e9a-bc76-1d2db75868d7

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Theorems.Thm_MeasureTheory_integral_directional_derivative_ball
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology

noncomputable section
namespace MixedGreenAnnulusWork

variable {n : ℕ}

/-- Smooth function vanishing near `x` and equal to one away from `x`. -/
def annCut (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.smoothTransition ((‖y - x‖ ^ 2 - r ^ 2 / 4) / (r ^ 2 / 4))

theorem annCut_contDiff (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : ContDiff ℝ 1 (annCut x r) := by
  apply Real.smoothTransition.contDiff.comp
  exact (((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const).div_const _

theorem annCut_eq_zero {x y : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hy : ‖y - x‖ < r / 2) : annCut x r y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have h0 := norm_nonneg (y - x)
  nlinarith

theorem annCut_eq_one {x y : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hy : 3 * r / 4 < ‖y - x‖) : annCut x r y = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem annCut_eventually_zero {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) :
    annCut x r =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [ball_mem_nhds x (half_pos hr)] with y hy
  exact annCut_eq_zero hr (by simpa [dist_eq_norm] using hy)

theorem mul_annCut_eventually_eq {x y : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hy : 3 * r / 4 < ‖y - x‖) :
    (fun z => annCut x r z * f z) =ᶠ[𝓝 y] f := by
  have ho : IsOpen {z : EuclideanSpace ℝ (Fin n) | 3 * r / 4 < ‖z - x‖} :=
    isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
  filter_upwards [ho.mem_nhds hy] with z hz
  rw [annCut_eq_one hr hz, one_mul]

theorem sphere_point_norm {x : EuclideanSpace ℝ (Fin n)} {s : ℝ} (hs : 0 < s)
    (ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : ‖x + s • ω.1 - x‖ = s := by
  have hω : ‖ω.1‖ = 1 := by simpa using ω.2
  rw [add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_of_nonneg hs.le]

theorem ball_ae_eq_closedBall (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : r ≠ 0) :
    ball x r =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] closedBall x r := by
  refine ae_eq_set.2 ⟨by simp [diff_eq_empty.2 ball_subset_closedBall], ?_⟩
  apply measure_mono_null _ (Measure.addHaar_sphere_of_ne_zero volume x hr)
  intro y hy
  simp only [mem_diff, mem_closedBall, mem_ball, not_lt] at hy
  exact le_antisymm hy.1 hy.2

theorem annulus_main {n : ℕ} (hn : 0 < n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : ∀ y ∈ Metric.closedBall x R, y ≠ x → ContDiffAt ℝ 1 f y)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ y in Metric.ball x R \ Metric.closedBall x r, fderiv ℝ f y v) =
      R ^ (n - 1) *
          (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            f (x + R • ω.1) * inner ℝ v ω.1 ∂volume.toSphere)
        - r ^ (n - 1) *
          (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            f (x + r • ω.1) * inner ℝ v ω.1 ∂volume.toSphere) := by
  have hR : 0 < R := hr.trans hrR
  set h : EuclideanSpace ℝ (Fin n) → ℝ := fun z => annCut x r z * f z with hh
  have hcd : ∀ y ∈ closedBall x R, ContDiffAt ℝ 1 h y := by
    intro y hy
    by_cases hyx : y = x
    · subst hyx
      have : h =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [annCut_eventually_zero (x := y) hr] with z hz
        simp [hh, hz]
      exact contDiffAt_const.congr_of_eventuallyEq this
    · exact (annCut_contDiff x r).contDiffAt.mul (hf y hy hyx)
  have hcdr : ∀ y ∈ closedBall x r, ContDiffAt ℝ 1 h y := fun y hy =>
    hcd y (closedBall_subset_closedBall hrR.le hy)
  have hballR := MeasureTheory.integral_directional_derivative_ball hn hR hcd v
  have hballr := MeasureTheory.integral_directional_derivative_ball hn hr hcdr v
  -- boundary values agree with `f`
  have hbdry : ∀ {s : ℝ}, r ≤ s → ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      h (x + s • ω.1) = f (x + s • ω.1) := by
    intro s hs ω
    have hs0 : 0 < s := hr.trans_le hs
    simp only [hh]
    rw [annCut_eq_one hr (by rw [sphere_point_norm hs0]; linarith), one_mul]
  simp only [hbdry hrR.le, hbdry le_rfl] at hballR hballr
  -- integrability of the derivative on the big ball
  have hcont : ContinuousOn (fun y => fderiv ℝ h y v) (closedBall x R) := by
    intro y hy
    exact (((hcd y hy).continuousAt_fderiv one_ne_zero).clm_apply
      continuousAt_const).continuousWithinAt
  have hint : IntegrableOn (fun y => fderiv ℝ h y v) (ball x R) :=
    (hcont.integrableOn_compact (isCompact_closedBall x R)).mono_set ball_subset_closedBall
  have hsub : closedBall x r ⊆ ball x R := closedBall_subset_ball hrR
  have hsplit := setIntegral_sdiff (μ := volume) measurableSet_closedBall hint hsub
  rw [← setIntegral_congr_set (ball_ae_eq_closedBall x hr.ne'), hballR, hballr] at hsplit
  rw [← hsplit]
  apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_closedBall)
  intro y hy
  have hy2 : r < ‖y - x‖ := by
    have := hy.2
    rw [mem_closedBall, not_le, dist_eq_norm] at this
    exact this
  have hev : h =ᶠ[𝓝 y] f := mul_annCut_eventually_eq hr f (y := y) (by linarith)
  change fderiv ℝ f y v = fderiv ℝ h y v
  rw [hev.fderiv_eq]

end MixedGreenAnnulusWork

open MeasureTheory

theorem solution {n : ℕ} (hn : 0 < n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : ∀ y ∈ Metric.closedBall x R, y ≠ x → ContDiffAt ℝ 1 f y)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ y in Metric.ball x R \ Metric.closedBall x r, fderiv ℝ f y v) =
      R ^ (n - 1) *
          (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            f (x + R • ω.1) * inner ℝ v ω.1 ∂volume.toSphere)
        - r ^ (n - 1) *
          (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            f (x + r • ω.1) * inner ℝ v ω.1 ∂volume.toSphere) :=
  MixedGreenAnnulusWork.annulus_main hn hr hrR hf v
