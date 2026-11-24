-- Prove2me | solution 1 for GlobalTheory.T.lintegral_four_sq_eq_mul_of_inversion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:36:03.103814+00:00
-- url     : https://prove2.me/submissions/c573a191-c5ce-4119-8fce-34083272dd42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralFourSq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralFourSqStatement
import Theorems.Thm_GlobalTheory_KSp_Planch_lintegral_four_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ C : ℝ, 0 < C → (∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x)) → ∀ φ ∈ SB X, ∫⁻ x, ‖four μ e φ x‖ₑ ^ 2 ∂μ = ENNReal.ofReal C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.KSp.Planch.lintegral_four_sq | exact GlobalTheory.KSp.Planch.lintegral_four_sq | (intros; apply GlobalTheory.KSp.Planch.lintegral_four_sq <;> assumption)
end _root_.GlobalTheory.T
