-- Prove2me | solution 1 for GlobalTheory.GramSchmidtCont.continuousOn_dOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:45:36.717527+00:00
-- url     : https://prove2.me/submissions/b57c7a28-8127-466f-a0ff-40c4d02e5912

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsContinuousGramSchmidt
import Theorems.Thm_GlobalTheory_GramSchmidtCont_continuous_gram
import Theorems.Thm_GlobalTheory_GramSchmidtCont_continuous_mat
import Theorems.Thm_GlobalTheory_GramSchmidtCont_continuousOn_uOf

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
theorem _root_.solution {r : ℕ} (X : Data E r) (τ : X.Ψ) (k : Fin r) :
    ContinuousOn (fun x : Frame X.Ψ r => dOf X x τ k) X.dom := by
  show ContinuousOn (fun x => gram τ.1 X.Gm (mat x τ * uOf X x τ) k k) X.dom
  exact ((continuous_id.matrix_elem k k).comp (continuous_gram τ.1 X.Gm)).comp_continuousOn
    ((continuous_mat X τ).continuousOn.mul (continuousOn_uOf X τ))
end GlobalTheory.GramSchmidtCont
