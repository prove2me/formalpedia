-- Prove2me | solution 1 for GlobalTheory.FirstMinimum.emb_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:42:13.525002+00:00
-- url     : https://prove2.me/submissions/d306de26-c223-4df2-a902-aa9910edd229

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
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.FirstMinimum
theorem _root_.solution {r : ℕ} (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    Data.emb τ (M.mulVec v) = (M.map τ).mulVec (Data.emb τ v) := by
  funext a
  simp [Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]
end GlobalTheory.FirstMinimum
