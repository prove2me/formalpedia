-- Prove2me | solution 1 for GlobalTheory.AbsFubini.lintegral_mul_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:02.983818+00:00
-- url     : https://prove2.me/submissions/aad5fc0a-c4bc-4a3e-9299-064b12acf3b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralKernelLiftsFubiniSigmaFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ENNReal
open GlobalTheory GlobalTheory.AbsFubini
variable {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
  {μ₁ : Measure X₁} {μ₂ : Measure X₂} {ν : Measure Y} [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]
namespace GlobalTheory.AbsFubini
theorem _root_.solution (ν : Measure Y) {a₁ a₂ : Y → ℝ≥0∞} (h₁ : Measurable a₁) (h₂ : Measurable a₂) :
    ∫⁻ y, a₁ y * a₂ y ∂ν ≤
      (∫⁻ y, a₁ y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) * (∫⁻ y, a₂ y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two h₁.aemeasurable
    h₂.aemeasurable
  simpa only [Pi.mul_apply] using h
end GlobalTheory.AbsFubini
