-- Prove2me | solution 1 for GlobalTheory.T.integral_mul_convolution_eq_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:10:09.990799+00:00
-- url     : https://prove2.me/submissions/a7ba50f7-0b59-4fb5-a45b-9c94d1a3a99d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulConvolutionEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulConvolutionEqStatement
import Theorems.Thm_GlobalTheory_integral_mul_convolution_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∀ κ a : H → ℂ, Continuous κ → HasCompactSupport κ → Measurable a → Integrable a μ → (∀ x ∉ K, a x = 0) → ∀ f : H → ℂ, Continuous f → ∫ z, f z * (∫ x, κ x * a (x⁻¹ * z) ∂μ) ∂μ = ∫ x, κ x * ∫ y, f (x * y) * a y ∂μ ∂μ := by
  first | exact @GlobalTheory.integral_mul_convolution_eq | exact GlobalTheory.integral_mul_convolution_eq | (intros; apply GlobalTheory.integral_mul_convolution_eq <;> assumption)
end _root_.GlobalTheory.T
