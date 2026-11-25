-- Prove2me | solution 1 for GlobalTheory.TwoLines.phla_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:11.015004+00:00
-- url     : https://prove2.me/submissions/ded37c39-47d5-478c-9424-42d98f6c5c29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
import Theorems.Thm_GlobalTheory_TwoLines_det_cpt
import Theorems.Thm_GlobalTheory_TwoLines_dmin_0
import Theorems.Thm_GlobalTheory_TwoLines_dmin_1
import Theorems.Thm_GlobalTheory_TwoLines_dmin_2
import Theorems.Thm_GlobalTheory_TwoLines_colSq_pos
import Theorems.Thm_GlobalTheory_TwoLines_cpt_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_phla_eq
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
theorem _root_.solution {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) {x0 : Frame X.Ψ 2} (hx : x0 ∈ X.dom)
    (la : Wt X.Ψ 2) (z : V (nd X)) :
    phla X la (cpt X x0 z) = ∑ τ, ((la τ 0 - la τ 1 : ℝ) * Real.log (colSq (cpt X x0 z) τ) +
      (la τ 1 : ℝ) * Real.log (‖(mat x0 τ).det‖ ^ 2)) := by
  rw [IW.phla_eq X (cpt_mem hG hp hx z)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hc := colSq_pos (cpt_mem hG hp hx z τ).1
  have e1 : (0 : Fin 2).succ = 1 := rfl
  have e2 : (0 : Fin 2).castSucc = 0 := rfl
  have e3 : (1 : Fin 2).succ = 2 := rfl
  have e4 : (1 : Fin 2).castSucc = 1 := rfl
  rw [Fin.sum_univ_two, e1, e2, e3, e4]
  simp only [IW.Lm, hG, dmin_0, dmin_1, dmin_2, det_cpt, Complex.norm_real, Real.norm_of_nonneg hc.le,
    norm_one, Real.log_one, Real.norm_of_nonneg (sq_nonneg ‖(mat x0 τ).det‖)]
  ring
end GlobalTheory.TwoLines
