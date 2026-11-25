-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.exists_coeff_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:46.94212+00:00
-- url     : https://prove2.me/submissions/b44c4ceb-6653-4116-b287-9502ad0fffdd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
  (x₀ : E)
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {η : ℝ} (hη : 0 < η) :
    ∃ δ, 0 < δ ∧ ∀ i, ∀ y ∈ Metric.closedBall x₀ (2 * δ), ‖a i y - a i x₀‖ ≤ η := by
  have hev : ∀ᶠ y in nhds x₀, ∀ i, a i y ∈ Metric.ball (a i x₀) η :=
    Filter.eventually_all.2 fun i ↦
      (a i).continuous.continuousAt.eventually_mem (Metric.ball_mem_nhds _ hη)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨ε / 4, by positivity, fun i y hy ↦ ?_⟩
  have hy' : y ∈ Metric.ball x₀ ε := by
    rw [Metric.mem_closedBall] at hy; rw [Metric.mem_ball]; linarith
  have := hball y hy' i
  rw [Metric.mem_ball, dist_eq_norm] at this
  exact this.le
end GroundTheory.Automorphic.Sobolev
