-- Prove2me | solution 1 for GlobalTheory.volume_preserving_ofLp_complex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:01.607804+00:00
-- url     : https://prove2.me/submissions/147c4fdf-648e-4452-aaa0-3a412dafcb16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped Nat ComplexConjugate
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (ι : Type*) [Fintype ι] :
    MeasurePreserving (@WithLp.ofLp 2 (ι → ℂ)) := by
  let e : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ) := PiLp.continuousLinearEquiv 2 ℝ fun _ : ι => ℂ
  change MeasurePreserving e
  refine ⟨e.continuous.measurable, ?_⟩
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map e volume = c • (volume : Measure (ι → ℂ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have h1 : ∫ w : ι → ℂ, ∏ i, exp (-1 * ‖w i‖ ^ 2) = π ^ Fintype.card ι := by
    rw [integral_fintype_prod_volume_eq_pow fun w : ℂ => exp (-1 * ‖w‖ ^ 2),
      integral_exp_neg_mul_norm_sq (E := ℂ) (g := 1) (by simp) one_pos]
    simp
  have h2 : ∫ w : ι → ℂ, ∏ i, exp (-1 * ‖w i‖ ^ 2) ∂(Measure.map e volume) =
      π ^ Fintype.card ι := by
    rw [integral_map e.continuous.measurable.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
    have := integral_exp_neg_mul_norm_sq (finrank_real_euclideanSpace_complex ι) one_pos
    rw [div_one] at this
    rw [← this]
    refine integral_congr_ae (.of_forall fun z => ?_)
    simp only
    rw [← exp_sum, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    rfl
  rw [hc, integral_smul_nnreal_measure, h1, NNReal.smul_def, smul_eq_mul,
    mul_eq_right₀ (by positivity)] at h2
  rw [hc, show c = 1 by exact_mod_cast h2, one_smul]
end GlobalTheory
