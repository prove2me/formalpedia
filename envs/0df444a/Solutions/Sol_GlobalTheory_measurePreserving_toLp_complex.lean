-- Prove2me | solution 1 for GlobalTheory.measurePreserving_toLp_complex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:54:43.05486+00:00
-- url     : https://prove2.me/submissions/27701f6c-37d4-4a09-840c-9a7eb12738a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Theorems.Thm_GlobalTheory_volume_ball_euclideanSpace_complex

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
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution :
    MeasurePreserving (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι) := by
  let e : (ι → ℂ) ≃L[ℂ] EuclideanSpace ℂ ι := (PiLp.continuousLinearEquiv 2 ℂ fun _ : ι => ℂ).symm
  have hm : Measurable (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι) := e.continuous.measurable
  have hH : ((volume : Measure (ι → ℂ)).map
      (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι)).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map volume
  have h := Measure.isAddLeftInvariant_eq_smul ((volume : Measure (ι → ℂ)).map
      (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι)) volume
  have hb : ((volume : Measure (ι → ℂ)).map
      (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι)) (ball 0 1) =
      volume (ball (0 : EuclideanSpace ℂ ι) 1) := by
    rw [Measure.map_apply hm measurableSet_ball, volume_ball_euclideanSpace_complex 0 one_pos]
    have h1 := Complex.volume_sum_rpow_lt_one ι (p := 2) one_le_two
    have h2 : (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι) ⁻¹' ball 0 1 =
        {x : ι → ℂ | ∑ i, ‖x i‖ ^ (2 : ℝ) < 1} := by
      ext x
      simp [EuclideanSpace.norm_eq, Real.sqrt_lt' one_pos]
    rw [h2, h1, mul_div_cancel_left₀ _ (two_ne_zero' ℝ), Real.Gamma_nat_eq_factorial]
    norm_num
  have h0 : volume (ball (0 : EuclideanSpace ℂ ι) 1) ≠ 0 := (measure_ball_pos _ 0 one_pos).ne'
  have ht : volume (ball (0 : EuclideanSpace ℂ ι) 1) ≠ ∞ := measure_ball_lt_top.ne
  refine ⟨hm, ?_⟩
  have h1 : Measure.addHaarScalarFactor ((volume : Measure (ι → ℂ)).map
      (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι)) volume = 1 := by
    rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hb
    exact_mod_cast (ENNReal.mul_eq_right h0 ht).1 hb
  rw [h, h1, one_smul]
end GlobalTheory
