-- Prove2me | solution 1 for GlobalTheory.DriftUnitary.cmType_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:23.101379+00:00
-- url     : https://prove2.me/submissions/e05a2a1b-033a-4eca-8406-c0809ad92073

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedFormsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDriftFunctionOrthonormalHermitianFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FrameStepOfRightMulRealUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDriftFunctionRealUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.DriftUnitary
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.DriftUnitary
theorem _root_.solution {r : ℕ} (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · refine ⟨⟨ComplexEmbedding.conjugate τ, ?_⟩⟩
    by_contra h'
    exact h ((X.cmType τ).2 h')
end GlobalTheory.DriftUnitary
