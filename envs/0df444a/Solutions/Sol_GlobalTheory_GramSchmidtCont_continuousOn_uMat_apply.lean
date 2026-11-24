-- Prove2me | solution 1 for GlobalTheory.GramSchmidtCont.continuousOn_uMat_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:10:55.443675+00:00
-- url     : https://prove2.me/submissions/0a87d847-7f55-402f-ab37-77de9bc9b128

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsContinuousGramSchmidt
import Theorems.Thm_GlobalTheory_GramSchmidtCont_continuousOn_inv_apply

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
namespace GlobalTheory.GramSchmidtCont
theorem _root_.solution {T : Type} [TopologicalSpace T] {n : ℕ} {s : Set T}
    {M : T → Matrix (Fin n) (Fin n) ℂ} (hM : Continuous M)
    (hd : ∀ t ∈ s, ∀ c : Fin n, (blk (M t) c).det ≠ 0) (j c : Fin n) :
    ContinuousOn (fun t => uMat (M t) j c) s := by
  by_cases hjc : j = c
  · simp only [uMat, Matrix.of_apply, if_pos hjc]
    exact continuousOn_const
  by_cases h : j < c
  · have hB : Continuous fun t => blk (M t) c := by
      unfold blk
      exact hM.matrix_submatrix _ _
    have hinv := fun m k => continuousOn_inv_apply hB (fun t ht => hd t ht c) m k
    simp only [uMat, Matrix.of_apply, if_neg hjc, dif_pos h, Matrix.vecMul, dotProduct, rowc]
    refine ContinuousOn.neg (continuousOn_finsetSum _ fun m _ => ContinuousOn.mul ?_ (hinv m _))
    exact (hM.matrix_elem c _).continuousOn
  · simp only [uMat, Matrix.of_apply, if_neg hjc, dif_neg h]
    exact continuousOn_const
end GlobalTheory.GramSchmidtCont
