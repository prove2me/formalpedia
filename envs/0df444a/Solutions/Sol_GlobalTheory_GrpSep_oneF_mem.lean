-- Prove2me | solution 1 for GlobalTheory.GrpSep.oneF_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:48:39.428553+00:00
-- url     : https://prove2.me/submissions/95e0077d-40cc-4507-a7d3-312154d2c2c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsLeNormDev
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
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.GrpSep
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.GrpSep
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) (r : ℕ) : oneF Ψ r ∈ Bor Ψ r := by
  intro τ
  refine ⟨?_, fun a c h => ?_⟩
  · change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · exact Matrix.one_apply_ne h.ne'
end GlobalTheory.GrpSep
