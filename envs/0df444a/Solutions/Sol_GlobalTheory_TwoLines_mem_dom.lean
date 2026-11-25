-- Prove2me | solution 1 for GlobalTheory.TwoLines.mem_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:18.910152+00:00
-- url     : https://prove2.me/submissions/cd753fac-42a7-478b-a581-8fd2f7bb1377

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
import Theorems.Thm_GlobalTheory_TwoLines_dmin_0
import Theorems.Thm_GlobalTheory_TwoLines_dmin_1
import Theorems.Thm_GlobalTheory_TwoLines_dmin_2
import Theorems.Thm_GlobalTheory_TwoLines_colSq_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
open GlobalTheory GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.TwoLines
theorem _root_.solution {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) (x : Frame X.Ψ 2) :
    x ∈ X.dom ↔ ∀ τ, (mat x τ).det ≠ 0 := by
  refine ⟨fun h τ => (h τ).1, fun h τ => ⟨h τ, fun i => ?_⟩⟩
  rw [hG, hp]
  fin_cases i
  · simp [psgn, dmin_0]
  · simpa [psgn, sgn, dmin_1] using colSq_pos (h τ)
  · have := h τ
    simp only [Fin.reduceFinMk, dmin_2, Complex.ofReal_re]
    simp [psgn, sgn, Finset.prod_range_succ, this]
end GlobalTheory.TwoLines
