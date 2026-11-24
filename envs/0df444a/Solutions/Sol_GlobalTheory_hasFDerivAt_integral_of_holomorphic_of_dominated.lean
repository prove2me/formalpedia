-- Prove2me | solution 1 for GlobalTheory.hasFDerivAt_integral_of_holomorphic_of_dominated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:55.092419+00:00
-- url     : https://prove2.me/submissions/3bd26edc-6a12-4102-a45b-6b09321d2cc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Theorems.Thm_GlobalTheory_aestronglyMeasurable_fderiv_of_param

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Metric Set
open scoped Topology Interval
open GlobalTheory
variable {T : Type*} [MeasurableSpace T] {μ : Measure T}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [FiniteDimensional ℂ E]
set_option linter.unusedSectionVars false
variable [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution {F : T → E → V} {x₀ : E} {s : Set E}
    {bound : T → ℝ} (hs : s ∈ 𝓝 x₀)
    (hmeas : ∀ y ∈ s, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableOn ℂ (F t) s)
    (hbound : ∀ᵐ t ∂μ, ∀ y ∈ s, ‖F t y‖ ≤ bound t) (hint : Integrable bound μ) :
    Integrable (fun t => F t x₀) μ ∧ Integrable (fun t => fderiv ℂ (F t) x₀) μ ∧
      HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x₀ ∂μ) x₀ := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  have hx₀ : x₀ ∈ s := mem_of_mem_nhds hs
  have hat : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀ := hdiff.mono fun t ht => ht.differentiableAt hs
  have hF₀ : Integrable (fun t => F t x₀) μ :=
    hint.mono' (hmeas x₀ hx₀) (hbound.mono fun t ht => ht x₀ hx₀)
  refine ⟨hF₀, ?_⟩
  refine hasFDerivAt_integral_of_dominated_loc_of_lip' (𝕜 := ℂ) (F := fun y t => F t y)
    (F' := fun t => fderiv ℂ (F t) x₀) (bound := fun t => 2 * bound t / r)
    (ball_mem_nhds x₀ hr) (fun y hy => hmeas y (hrs hy)) hF₀
    (aestronglyMeasurable_fderiv_of_param (Filter.mem_of_superset hs hmeas) hat) ?_
    ((hint.const_mul 2).div_const r) (hat.mono fun t ht => ht.hasFDerivAt)
  filter_upwards [hdiff, hbound] with t ht hb y hy
  have hmaps : MapsTo (F t) (ball x₀ r) (closedBall (F t x₀) (2 * bound t)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hb z (hrs hz)
    have h2 := hb x₀ hx₀
    linarith [norm_sub_le (F t z) (F t x₀)]
  simpa [dist_eq_norm] using
    Complex.dist_le_div_mul_dist_of_mapsTo_ball (ht.mono hrs) hmaps hy
end GlobalTheory
