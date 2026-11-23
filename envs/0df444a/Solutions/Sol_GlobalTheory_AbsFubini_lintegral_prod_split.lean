-- Prove2me | solution 1 for GlobalTheory.AbsFubini.lintegral_prod_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:27.619871+00:00
-- url     : https://prove2.me/submissions/860d04e2-6fcb-4269-9fc5-6b1433f0ba47

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
theorem _root_.solution {a₁ : X₁ → Y → ℝ≥0∞} {a₂ : X₂ → Y → ℝ≥0∞}
    (ha₁ : Measurable (Function.uncurry a₁)) (ha₂ : Measurable (Function.uncurry a₂)) (y : Y) :
    (∫⁻ x₁, a₁ x₁ y ∂μ₁) * (∫⁻ x₂, a₂ x₂ y ∂μ₂) = ∫⁻ p : X₁ × X₂, a₁ p.1 y * a₂ p.2 y ∂μ₁.prod μ₂ := by
  have m₁ : Measurable fun x => a₁ x y := ha₁.comp (measurable_id.prodMk measurable_const)
  have m₂ : Measurable fun x => a₂ x y := ha₂.comp (measurable_id.prodMk measurable_const)
  exact (lintegral_prod_mul (f := fun x => a₁ x y) (g := fun x => a₂ x y) m₁.aemeasurable
    m₂.aemeasurable).symm
end GlobalTheory.AbsFubini
