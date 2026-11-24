-- Prove2me | solution 1 for GlobalTheory.T.right_translation_curve_sq_le_and_integral_deriv_eq_zero_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:18.630949+00:00
-- url     : https://prove2.me/submissions/68893122-a0a7-445d-9387-b8bdf19d8c67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RightTranslationCurveSqLeAndIntegralDerivEqZeroA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RightTranslationCurveSqLeAndIntegralDerivEqZeroAStatement
import Theorems.Thm_GlobalTheory_right_translation_curve_sq_le_and_integral_deriv_eq_zero


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (c : ℝ → K), Continuous c → c 0 = 1 → ∀ f f' : K → ℂ, Continuous f → Continuous f' → (∀ x t, HasDerivAt (fun t : ℝ => f (x * c t)) (f' (x * c t)) t) → (∫ x, ‖f (x * c 1) - f x‖ ^ 2 ∂μ ≤ ∫ x, ‖f' x‖ ^ 2 ∂μ) ∧ ∫ x, f' x ∂μ = 0 := by
  first | exact @GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero | exact GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero | (intros; apply GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero <;> assumption)
end _root_.GlobalTheory.T
