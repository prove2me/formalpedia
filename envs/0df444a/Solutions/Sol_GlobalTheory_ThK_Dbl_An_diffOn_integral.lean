-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.An.diffOn_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:41:35.565359+00:00
-- url     : https://prove2.me/submissions/69e2765e-cc06-4d1c-9227-3155ef359f4c

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_UnfoldA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.An
open MeasureTheory Filter Topology
namespace GlobalTheory.ThK.Dbl.An
theorem _root_.solution {X : Type} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U)
    {k : ℂ → X → ℂ} (hm : ∀ s ∈ U, AEStronglyMeasurable (k s) μ) (hd : ∀ x, DifferentiableOn ℂ (k · x) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ, ∀ s ∈ K, ∀ x, ‖k s x‖ ≤ C) :
    DifferentiableOn ℂ (fun s => ∫ x, k s x ∂μ) U := by
  intro s₀ h₀
  obtain ⟨r, hr, hU'⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds h₀)
  obtain ⟨C, hC⟩ := hb _ hU' (isCompact_closedBall s₀ r)
  have sub : ∀ s ∈ Metric.ball s₀ (r / 2), Metric.closedBall s (r / 2) ⊆ Metric.closedBall s₀ r := fun s hs =>
    Metric.closedBall_subset_closedBall' (by have := Metric.mem_ball.1 hs; linarith)
  have da : ∀ x, ∀ s ∈ U, HasDerivAt (k · x) (deriv (k · x) s) s := fun x s hs =>
    ((hd x).differentiableAt (hU.mem_nhds hs)).hasDerivAt
  have m' : AEStronglyMeasurable (fun x => deriv (k · x) s₀) μ := by
    classical
    refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] s₀) (f := fun s x => if s ∈ U then slope (k · x) s₀ s else 0) (fun s => ?_)
      (.of_forall fun x => (hasDerivAt_iff_tendsto_slope.1 (da x s₀ h₀)).congr' ?_)
    · by_cases hs : s ∈ U
      · simp only [if_pos hs, slope_def_module]
        exact ((hm s hs).sub (hm s₀ h₀)).const_smul (s - s₀)⁻¹
      · simp only [if_neg hs]; exact aestronglyMeasurable_const
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds h₀)] with s hs using (if_pos hs).symm
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (bound := fun _ => C / (r / 2)) (F := k)
    (F' := fun s x => deriv (k · x) s) (Metric.ball_mem_nhds s₀ (half_pos hr))
    (mem_of_superset (hU.mem_nhds h₀) hm) ?_ m' (.of_forall fun x s hs => ?_) (integrable_const _)
    (.of_forall fun x s hs => da x s (hU' (sub s hs (Metric.mem_closedBall_self (half_pos hr).le))))).2.differentiableAt.differentiableWithinAt
  · exact .of_bound (hm s₀ h₀) C (.of_forall (hC s₀ (Metric.mem_closedBall_self hr.le)))
  · exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hr)
      (((hd x).mono ((sub s hs).trans hU')).diffContOnCl_ball subset_rfl)
      fun z hz => hC z (sub s hs (Metric.sphere_subset_closedBall hz)) x
end GlobalTheory.ThK.Dbl.An
