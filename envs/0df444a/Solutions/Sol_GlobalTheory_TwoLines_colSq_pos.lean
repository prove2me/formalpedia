-- Prove2me | solution 1 for GlobalTheory.TwoLines.colSq_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:43.288478+00:00
-- url     : https://prove2.me/submissions/30c47f5f-160a-4f48-9aca-bd98f10e19de

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
import Theorems.Thm_GlobalTheory_TwoLines_det_mat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
open GlobalTheory GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.TwoLines
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} {x : Frame Ψ 2} {τ : Ψ} (h : (mat x τ).det ≠ 0) :
    0 < colSq x τ := by
  rw [det_mat] at h
  by_contra hn
  have h0 : x τ 0 0 = 0 := by
    rw [← norm_eq_zero]; unfold colSq at hn; nlinarith [sq_nonneg ‖x τ 0 0‖, sq_nonneg ‖x τ 1 0‖]
  have h1 : x τ 1 0 = 0 := by
    rw [← norm_eq_zero]; unfold colSq at hn; nlinarith [sq_nonneg ‖x τ 0 0‖, sq_nonneg ‖x τ 1 0‖]
  apply h
  rw [h0, h1]; ring
end GlobalTheory.TwoLines
