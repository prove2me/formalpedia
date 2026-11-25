-- Prove2me | solution 1 for GlobalTheory.GramSchmidtCont.continuousOn_sOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:31:59.537366+00:00
-- url     : https://prove2.me/submissions/32d59f58-1729-457a-b988-6bcb81d577ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsContinuousGramSchmidt
import Theorems.Thm_GlobalTheory_GramSchmidtCont_continuousOn_dOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_abs_re_pos


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
    ContinuousOn (fun x : Frame X.Ψ r => sOf X x τ k) X.dom := by
  show ContinuousOn (fun x => (((Real.sqrt |(dOf X x τ k).re|)⁻¹ : ℝ) : ℂ)) X.dom
  refine Complex.continuous_ofReal.comp_continuousOn (ContinuousOn.inv₀ ?_ ?_)
  · exact Real.continuous_sqrt.comp_continuousOn (continuous_abs.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn (continuousOn_dOf X τ k)))
  · intro x hx
    exact (Real.sqrt_pos.2 (abs_re_pos X hx τ k)).ne'
end GlobalTheory.GramSchmidtCont
