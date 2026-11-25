-- Prove2me | solution 1 for GlobalTheory.GramSchmidtCont.continuousOn_bOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:42:53.156021+00:00
-- url     : https://prove2.me/submissions/026a876d-d391-4d66-a6d8-47075078ec50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsContinuousGramSchmidt
import Theorems.Thm_GlobalTheory_GramSchmidtCont_continuousOn_uOf
import Theorems.Thm_GlobalTheory_GramSchmidtCont_continuousOn_sOf

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
theorem _root_.solution {r : ℕ} (X : Data E r) : ContinuousOn (bOf X) X.dom := by
  refine continuousOn_pi.2 fun τ => ?_
  show ContinuousOn (fun x => (uOf X x τ * Matrix.diagonal (sOf X x τ) : Matrix (Fin r) (Fin r) ℂ)) X.dom
  exact (continuousOn_uOf X τ).mul (continuous_id.matrix_diagonal.comp_continuousOn
    (continuousOn_pi.2 fun k => continuousOn_sOf X τ k))
end GlobalTheory.GramSchmidtCont
