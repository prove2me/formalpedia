-- Prove2me | solution 1 for GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:35:25.912918+00:00
-- url     : https://prove2.me/submissions/d3682d9a-31e3-453f-b2b5-30b50a7dd704

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RightTranslationCurveSqLeAndIntegralDerivEqZeroA
import Theorems.Thm_GlobalTheory_integral_intervalIntegral_mul_right_curve
import Theorems.Thm_GlobalTheory_norm_intervalIntegral_unit_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (c : ℝ → K), Continuous c → c 0 = 1 →
      ∀ f f' : K → ℂ, Continuous f → Continuous f' →
      (∀ x t, HasDerivAt (fun t : ℝ => f (x * c t)) (f' (x * c t)) t) →
      (∫ x, ‖f (x * c 1) - f x‖ ^ 2 ∂μ ≤ ∫ x, ‖f' x‖ ^ 2 ∂μ) ∧ ∫ x, f' x ∂μ = 0 := by
  intro K _ _ _ _ _ _ _ μ _ _ _ c hc h0 f f' hf hf' hd
  have key : ∀ x, f (x * c 1) - f x = ∫ t in (0:ℝ)..1, f' (x * c t) := by
    intro x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd x t)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp [h0]
  have hI : ∀ {E : Type} [NormedAddCommGroup E] [SecondCountableTopology E] (g : K → E),
      Continuous g → Integrable g μ :=
    fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  constructor
  · rw [← integral_intervalIntegral_mul_right_curve μ c hc (fun x => ‖f' x‖ ^ 2) (by fun_prop)]
    refine integral_mono (hI _ (by fun_prop)) (hI _ ?_) fun x => ?_
    · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun (x : K) (t : ℝ) => ‖f' (x * c t)‖ ^ 2)
        (by unfold Function.uncurry; fun_prop) 0 1
    · simp only [key]
      exact norm_intervalIntegral_unit_sq_le _ (by fun_prop)
  · rw [← integral_intervalIntegral_mul_right_curve μ c hc f' hf']
    simp_rw [← key]
    rw [integral_sub (hI _ (by fun_prop)) (hI _ hf), integral_mul_right_eq_self f, sub_self]
end GlobalTheory
