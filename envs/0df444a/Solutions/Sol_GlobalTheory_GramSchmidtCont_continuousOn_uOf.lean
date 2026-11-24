-- Prove2me | solution 1 for GlobalTheory.GramSchmidtCont.continuousOn_uOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:27:51.900023+00:00
-- url     : https://prove2.me/submissions/be94f251-42ed-4427-bcf6-01681bcc8ef0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsContinuousGramSchmidt
import Theorems.Thm_GlobalTheory_GramSchmidtCont_continuousOn_uMat_apply
import Theorems.Thm_GlobalTheory_GramSchmidtCont_continuous_gram
import Theorems.Thm_GlobalTheory_GramSchmidtCont_continuous_mat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_blk_det


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
open GlobalTheory GlobalTheory.GramSchmidtCont
open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.GramSchmidtCont
theorem _root_.solution {r : ℕ} (X : Data E r) (τ : X.Ψ) :
    ContinuousOn (fun x : Frame X.Ψ r => uOf X x τ) X.dom := by
  refine continuousOn_pi.2 fun j => continuousOn_pi.2 fun c => ?_
  exact continuousOn_uMat_apply ((continuous_gram τ.1 X.Gm).comp (continuous_mat X τ))
    (fun x hx c => blk_det X hx τ c) j c
end GlobalTheory.GramSchmidtCont
