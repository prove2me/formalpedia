-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.integral_comp_mp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:07.708016+00:00
-- url     : https://prove2.me/submissions/d236b81e-dceb-43a0-97cd-129ef1c2cd67

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
theorem _root_.solution {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ρ : Measure Y}
    {T : X → Y} (hT : MeasurePreserving T μ ρ) {f : Y → ℂ} (hf : AEStronglyMeasurable f ρ) :
    ∫ x, f (T x) ∂μ = ∫ y, f y ∂ρ := by
  rw [← integral_map hT.measurable.aemeasurable (by rwa [hT.map_eq]), hT.map_eq]
end GlobalTheory.RootEx.QuotStep
