-- Prove2me | solution 1 for GlobalTheory.GramSchmidtCont.continuous_gram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:02.958841+00:00
-- url     : https://prove2.me/submissions/ca1a27c3-3195-4c93-815f-ee82595942a9

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
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.GramSchmidtCont
theorem _root_.solution {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) :
    Continuous (gram τ G) := by
  refine continuous_matrix fun a b => ?_
  simp only [gram, hermC, col, Matrix.of_apply]
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    ((continuous_id.matrix_elem k a).mul continuous_const).mul
      (Complex.continuous_conj.comp (continuous_id.matrix_elem l b))
end GlobalTheory.GramSchmidtCont
