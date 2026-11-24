-- Prove2me | solution 1 for GlobalTheory.JR.FourUnit.integral_ball_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:14:13.672372+00:00
-- url     : https://prove2.me/submissions/0c1a6db3-1114-40c1-a618-451a6234240b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockUnitIndicator
import Theorems.Thm_GlobalTheory_JR_FourUnit_integral_indicator_char_eq_zero
import Theorems.Thm_GlobalTheory_JR_FourUnit_norm_trace_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.FourUnit
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.FourUnit
theorem _root_.solution (hU : Unram F E) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (hvol : μ (Metric.closedBall 0 1) = 1) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (htr : ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y)
    (hu : ∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1) (y : E) :
    ∫ z, (Metric.closedBall (0 : E) 1).indicator (fun z => ψ (Algebra.trace F E (star z * y))) z ∂μ =
      if ‖y‖ ≤ 1 then 1 else 0 := by
  haveI := hU.ultraE
  haveI := hU.ultraF
  split_ifs with hy
  · rw [Set.indicator_congr (g := fun _ => (1 : ℂ)) (fun z hz => ?_)]
    · rw [integral_indicator measurableSet_closedBall, setIntegral_const]
      simp [Measure.real, hvol]
    · apply hψ.1
      refine (norm_trace_le hU htr _).trans ?_
      rw [norm_mul, hU.norm_star]
      exact mul_le_one₀ (mem_closedBall_zero_iff.1 hz) (norm_nonneg _) hy
  · push_neg at hy
    obtain ⟨x₀, hx₀, hx₀'⟩ := hψ.2
    obtain ⟨yF, hyF⟩ := hU.unram y
    obtain ⟨u, hu1, hu2⟩ := hu
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
    have hyF0 : yF ≠ 0 := by rintro rfl; rw [hyF] at hy; simp at hy; linarith
    have hx₀y : ‖x₀‖ ≤ ‖y‖ := by
      have h1 : ‖yF⁻¹‖ < 1 := by rw [norm_inv, ← hyF]; exact inv_lt_one_of_one_lt₀ hy
      have h2 := hx₀' _ h1
      rw [norm_mul, norm_inv, ← hyF] at h2
      have hpos : 0 < ‖y‖ := by linarith
      rwa [mul_inv_le_iff₀ hpos, one_mul] at h2
    have htu : Algebra.trace F E u ≠ 0 := by intro h; rw [h, norm_zero] at hu2; exact zero_ne_one hu2
    set w : E := (x₀ / Algebra.trace F E u) • u with hw
    have hTw : Algebra.trace F E w = x₀ := by
      rw [hw, LinearMap.map_smul, smul_eq_mul, div_mul_cancel₀ _ htu]
    have hnw : ‖w‖ ≤ ‖y‖ := by
      rw [hw, norm_smul, norm_div, hu2, div_one]
      exact (mul_le_of_le_one_right (norm_nonneg _) hu1).trans hx₀y
    have hpos : 0 < ‖y‖ := by linarith
    refine integral_indicator_char_eq_zero μ _ _ (fun a b => ?_) (star (w * y⁻¹)) (fun z => ?_) ?_
    · rw [star_add, add_mul, map_add, AddChar.map_add_eq_mul]
    · have ht : ‖star (w * y⁻¹)‖ ≤ 1 := by
        rw [hU.norm_star, norm_mul, norm_inv, mul_inv_le_iff₀ hpos, one_mul]; exact hnw
      simp only [mem_closedBall_zero_iff]
      constructor
      · intro h
        have := IsUltrametricDist.norm_add_le_max (star (w * y⁻¹) + z) (-(star (w * y⁻¹)))
        rw [norm_neg, show star (w * y⁻¹) + z + -star (w * y⁻¹) = z by abel] at this
        exact this.trans (max_le h ht)
      · intro h
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ht h)
    · simp only [star_star]
      rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one, hTw]
      exact hx₀
end GlobalTheory.JR.FourUnit
