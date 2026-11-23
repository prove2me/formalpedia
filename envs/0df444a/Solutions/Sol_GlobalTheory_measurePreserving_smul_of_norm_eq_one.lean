-- Prove2me | solution 1 for GlobalTheory.measurePreserving_smul_of_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:26.664435+00:00
-- url     : https://prove2.me/submissions/8c6c577a-73f4-4c2c-870e-902310a22628

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set
open scoped ENNReal Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] {c : ℂ}
    (hc : ‖c‖ = 1) : MeasurePreserving (fun z : E => c • z) μ μ := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have hm : Measurable fun z : E => c • z := (continuous_const_smul c).measurable
  let e : E ≃L[ℂ] E := (LinearEquiv.smulOfNeZero ℂ E c hc0).toContinuousLinearEquiv
  have hH : (μ.map fun z : E => c • z).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have h := Measure.isAddLeftInvariant_eq_smul (μ.map fun z : E => c • z) μ
  have hb : (μ.map fun z : E => c • z) (ball 0 1) = μ (ball 0 1) := by
    rw [Measure.map_apply hm measurableSet_ball]
    congr 1
    ext z
    simp [norm_smul, hc]
  have h0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have ht : μ (ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  refine ⟨hm, ?_⟩
  have h1 : Measure.addHaarScalarFactor (μ.map fun z : E => c • z) μ = 1 := by
    rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hb
    exact_mod_cast (ENNReal.mul_eq_right h0 ht).1 hb
  rw [h, h1, one_smul]
end GlobalTheory
