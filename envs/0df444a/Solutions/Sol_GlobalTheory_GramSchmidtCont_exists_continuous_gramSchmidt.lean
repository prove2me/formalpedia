-- Prove2me | solution 1 for GlobalTheory.GramSchmidtCont.exists_continuous_gramSchmidt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:58:00.986726+00:00
-- url     : https://prove2.me/submissions/f316de5c-c7be-4ed7-b800-87e7246c72bc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsContinuousGramSchmidt
import Theorems.Thm_GlobalTheory_GramSchmidtCont_continuousOn_bOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_bOf_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_ortho_bOf


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
theorem _root_.solution :
    (∀ (r : ℕ) (X : Data E r), ∃ β : Frame X.Ψ r → Frame X.Ψ r, ContinuousOn β X.dom ∧
      ∀ x ∈ X.dom, β x ∈ Bor X.Ψ r ∧ IsOrth X (rmul x (β x))) := by
  intro r X
  exact ⟨bOf X, continuousOn_bOf X, fun x hx => ⟨bOf_mem X hx, ortho_bOf X hx⟩⟩
end GlobalTheory.GramSchmidtCont
