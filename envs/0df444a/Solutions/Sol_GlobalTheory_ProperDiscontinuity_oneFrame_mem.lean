-- Prove2me | solution 1 for GlobalTheory.ProperDiscontinuity.oneFrame_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:38:49.751853+00:00
-- url     : https://prove2.me/submissions/512d1e68-6bce-41ef-8071-e054712cfa77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RmulOneFrame
import Theorems.Thm_GlobalTheory_ProperDiscontinuity_mat_oneFrame

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
open GlobalTheory GlobalTheory.ProperDiscontinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.ProperDiscontinuity
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) (r : ℕ) : oneFrame Ψ r ∈ Bor Ψ r := by
  intro τ
  refine ⟨by rw [mat_oneFrame]; simp, fun a c h => ?_⟩
  exact Matrix.one_apply_ne (ne_of_gt h)
end GlobalTheory.ProperDiscontinuity
