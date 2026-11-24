-- Prove2me | solution 1 for GlobalTheory.integrableOn_log_norm_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:32:41.667863+00:00
-- url     : https://prove2.me/submissions/3eeb09f6-a438-450a-9465-89ca326e4ca7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableOnOfNormLeSumAbsLogAddLogLog
import Theorems.Thm_GlobalTheory_integrableOn_log_norm_ball_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℂ} {a : E}
    {r M : ℝ} (hf : DifferentiableOn ℂ f (ball a r)) (hM : ∀ z ∈ ball a r, ‖f z‖ ≤ M)
    (h0 : f a ≠ 0) :
    (∀ᵐ z ∂(μ.restrict (ball a r)), f z ≠ 0) ∧
      IntegrableOn (fun z => Real.log ‖f z‖) (ball a r) μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have hm : MapsTo (fun z : E => z + a) (ball 0 r) (ball a r) := fun z hz => by simpa using hz
  obtain ⟨h1, h2⟩ := integrableOn_log_norm_ball_zero μ (f := fun z => f (z + a)) (r := r) (M := M)
    (hf.comp (by fun_prop) hm) (fun z hz => hM _ (hm hz)) (by simpa using h0)
  have hp : MeasurePreserving (fun z : E => z - a) (μ.restrict (ball a r))
      (μ.restrict (ball 0 r)) := by
    have := (measurePreserving_sub_right μ a).restrict_preimage (s := ball 0 r) measurableSet_ball
    convert this using 2
    ext z
    simp [dist_eq_norm]
  refine ⟨?_, ?_⟩
  · simpa using hp.quasiMeasurePreserving.ae h1
  · simpa [Function.comp_def, IntegrableOn] using hp.integrable_comp_of_integrable h2
end GlobalTheory
