-- Prove2me | solution 1 for GlobalTheory.T.integral_fold_via_lintegral_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:21:43.722729+00:00
-- url     : https://prove2.me/submissions/8d28732a-cd22-4787-8bfa-681f10f485e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralFoldViaLintegralFormula
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralFoldViaLintegralFormulaStatement
import Theorems.Thm_GlobalTheory_FoldIntegral_fold


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
theorem _root_.solution : ∀ {α Y Z : Type} [MeasurableSpace α] [MeasurableSpace Y] [MeasurableSpace Z] (μ : Measure α) (Fs : Set α) (ν : Measure Y) (m : Measure Z) (S : Set Z), m S < ⊤ → ∀ (Φ : Y → Z → α), Measurable (Function.uncurry Φ) → ∀ (c : ℝ), 0 ≤ c → ∀ (P : (α → ENNReal) → Prop), (∀ F : α → ENNReal, Measurable F → P F → ∫⁻ x in Fs, F x ∂μ = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in S, F (Φ y s) ∂m ∂ν) → ∀ (G : α → ℂ), Measurable G → (∀ φ : ℂ → ENNReal, φ 0 = 0 → P (fun x => φ (G x))) → ∫⁻ y, ∫⁻ s in S, ‖G (Φ y s)‖ₑ ∂m ∂ν < ⊤ → IntegrableOn G Fs μ ∧ ∫ x in Fs, G x ∂μ = (c : ℂ) * ∫ y, ∫ s in S, G (Φ y s) ∂m ∂ν := by
  first | exact @GlobalTheory.FoldIntegral.fold | exact GlobalTheory.FoldIntegral.fold | (intros; apply GlobalTheory.FoldIntegral.fold <;> assumption)
end _root_.GlobalTheory.T
