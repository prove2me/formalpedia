-- Prove2me | solution 1 for GlobalTheory.FirstMinimum.cmType_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:42:05.979279+00:00
-- url     : https://prove2.me/submissions/a46a126c-5b65-4a9b-80df-fcde7cca36e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MinimumGrowthBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.FirstMinimum
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.FirstMinimum
theorem _root_.solution {r : ℕ} (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · have h' : ComplexEmbedding.conjugate τ ∈ X.Ψ := by
      by_contra h2
      exact h ((X.cmType τ).mpr h2)
    exact ⟨⟨_, h'⟩⟩
end GlobalTheory.FirstMinimum
