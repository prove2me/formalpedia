-- Prove2me | solution 1 for GlobalTheory.LineCos.exists_lintegral_le_iterated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:45:07.705366+00:00
-- url     : https://prove2.me/submissions/19bbac9d-3df4-4aec-b24a-6d8d6d091e5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniformStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalDensityBoundNearPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LineCos
namespace GlobalTheory.LineCos
theorem _root_.solution (d : ℕ) : ∃ c : ENNReal, c ≠ ⊤ ∧ ∀ F : V (d + 1) → ENNReal,
    ∫⁻ z, F z ≤ c * ∫⁻ b : Fin d → ℂ, ∫⁻ x : ℂ, F ((splitLin d).symm (b, x)) := by
  let e : V (d + 1) ≃L[ℝ] (Fin d → ℂ) × ℂ := (splitLin d).toContinuousLinearEquiv
  let em : V (d + 1) ≃ᵐ (Fin d → ℂ) × ℂ := e.toHomeomorph.toMeasurableEquiv
  haveI : Measure.IsAddHaarMeasure (Measure.map e (volume : Measure (V (d + 1)))) := inferInstance
  haveI : Measure.IsAddHaarMeasure (volume : Measure ((Fin d → ℂ) × ℂ)) :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin d → ℂ)) (volume : Measure ℂ)
  have h := Measure.isAddLeftInvariant_eq_smul (Measure.map e (volume : Measure (V (d + 1))))
    (volume : Measure ((Fin d → ℂ) × ℂ))
  refine ⟨Measure.addHaarScalarFactor (Measure.map e (volume : Measure (V (d + 1))))
    (volume : Measure ((Fin d → ℂ) × ℂ)), ENNReal.coe_ne_top, fun F => ?_⟩
  have h1 : ∫⁻ z, F z = ∫⁻ p, F (e.symm p) ∂(Measure.map e (volume : Measure (V (d + 1)))) := by
    have := lintegral_map_equiv (μ := (volume : Measure (V (d + 1)))) (fun p => F (e.symm p)) em
    simpa [em] using this.symm
  rw [h1]
  conv_lhs => rw [h]
  rw [lintegral_smul_measure]
  refine mul_le_mul_right ?_ _
  exact lintegral_prod_le (μ := (volume : Measure (Fin d → ℂ))) (ν := (volume : Measure ℂ)) (fun p => F (e.symm p))
end GlobalTheory.LineCos
