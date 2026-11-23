-- Prove2me | solution 1 for GlobalTheory.GramSchmidtCont.continuous_mat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:03.151313+00:00
-- url     : https://prove2.me/submissions/5b55cd03-843c-4696-a5de-fe1e9706c61d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsContinuousGramSchmidt

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
    Continuous (fun x : Frame X.Ψ r => mat x τ) := by
  refine continuous_matrix fun a b => ?_
  simp only [mat, Matrix.of_apply]
  exact (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
end GlobalTheory.GramSchmidtCont
