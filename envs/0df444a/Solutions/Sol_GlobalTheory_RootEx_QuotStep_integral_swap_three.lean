-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.integral_swap_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:03:11.84571+00:00
-- url     : https://prove2.me/submissions/0c027180-024d-456c-b148-123822246d3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotStep
namespace GlobalTheory.RootEx.QuotStep
theorem _root_.solution {X B U : Type} [MeasurableSpace X] [MeasurableSpace B] [MeasurableSpace U]
    (μ : Measure X) (β : Measure B) (ρ : Measure U) [SFinite μ] [SFinite β] [SFinite ρ]
    (Φ : X × (B × U) → ℂ) (hΦ : Integrable Φ (μ.prod (β.prod ρ))) :
    ∫ x, ∫ y, Φ (x, y) ∂(β.prod ρ) ∂μ = ∫ b, ∫ x, ∫ u, Φ (x, (b, u)) ∂ρ ∂μ ∂β := by
  have h1 : ∫ x, ∫ y, Φ (x, y) ∂(β.prod ρ) ∂μ = ∫ x, ∫ b, ∫ u, Φ (x, (b, u)) ∂ρ ∂β ∂μ :=
    integral_congr_ae (hΦ.prod_right_ae.mono fun x hx => integral_prod _ hx)
  have h2 : Integrable (Φ ∘ MeasurableEquiv.prodAssoc) ((μ.prod β).prod ρ) :=
    ((measurePreserving_prodAssoc μ β ρ).integrable_comp_emb
      MeasurableEquiv.prodAssoc.measurableEmbedding).2 hΦ
  rw [h1]
  exact integral_integral_swap (f := fun x b => ∫ u, Φ (x, (b, u)) ∂ρ) h2.integral_prod_left
end GlobalTheory.RootEx.QuotStep
