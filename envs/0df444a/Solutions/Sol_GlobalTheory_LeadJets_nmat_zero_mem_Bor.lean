-- Prove2me | solution 1 for GlobalTheory.LeadJets.nmat_zero_mem_Bor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:46:46.585021+00:00
-- url     : https://prove2.me/submissions/fbd5f933-1ce1-44b9-856b-b08648c437fc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NmatZeroMemBor
import Theorems.Thm_GlobalTheory_LeadJets_mat_nmat_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics
open GlobalTheory GlobalTheory.LeadJets
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LeadJets
theorem _root_.solution {r : ℕ} (X : Data E r) : nmat X 0 ∈ Bor X.Ψ r := by
  intro τ
  refine ⟨by rw [mat_nmat_zero, Matrix.det_one]; exact one_ne_zero, fun a c h => ?_⟩
  have := congrFun (congrFun (mat_nmat_zero X τ) a) c
  rw [Matrix.one_apply_ne h.ne'] at this
  exact this
end GlobalTheory.LeadJets
