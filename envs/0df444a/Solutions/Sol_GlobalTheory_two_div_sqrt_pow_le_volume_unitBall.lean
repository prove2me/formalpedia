-- Prove2me | solution 1 for GlobalTheory.two_div_sqrt_pow_le_volume_unitBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:59:27.945938+00:00
-- url     : https://prove2.me/submissions/07ec1d10-3c53-4539-a250-04fe0e1ed00d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
noncomputable section
open Module Submodule MeasureTheory
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (E)
namespace GlobalTheory
theorem _root_.solution :
    (2 / √(finrank ℝ E : ℝ)) ^ finrank ℝ E ≤ volume.real (Metric.ball (0 : E) 1) := by
  let o := stdOrthonormalBasis ℝ E
  let f : E →ₗ[ℝ] (Fin (finrank ℝ E) → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin (finrank ℝ E) → ℝ)).toLinearMap ∘ₗ o.repr.toLinearEquiv.toLinearMap
  have hf : MeasurePreserving f := (PiLp.volume_preserving_ofLp _).comp o.measurePreserving_repr
  set r : ℝ := (√(finrank ℝ E : ℝ))⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hs : volume (f ⁻¹' Metric.closedBall 0 r) = ENNReal.ofReal ((2 * r) ^ finrank ℝ E) := by
    rw [hf.measure_preimage Metric.isClosed_closedBall.measurableSet.nullMeasurableSet,
      Real.volume_pi_closedBall _ hr0, Fintype.card_fin]
  have hsub : f ⁻¹' Metric.closedBall 0 r ⊆ Metric.closedBall (0 : E) 1 := by
    intro x hx
    have hi : ∀ i, ‖o.repr x i‖ ≤ r := fun i ↦
      (pi_norm_le_iff_of_nonneg hr0).1 (mem_closedBall_zero_iff.1 hx) i
    rw [mem_closedBall_zero_iff, ← sq_le_one_iff₀ (norm_nonneg _), ← o.repr.norm_map,
      EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖o.repr x i‖ ^ 2 ≤ ∑ _i : Fin (finrank ℝ E), r ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ by have := hi i; gcongr
      _ = finrank ℝ E * (finrank ℝ E : ℝ)⁻¹ := by simp [hr]
      _ ≤ 1 := mul_inv_le_one
  have h := measure_mono (μ := volume) hsub
  rw [hs, Measure.addHaar_unitClosedBall_eq_addHaar_unitBall,
    ENNReal.ofReal_le_iff_le_toReal measure_ball_lt_top.ne] at h
  rwa [div_eq_mul_inv]
end GlobalTheory
