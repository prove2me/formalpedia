-- Prove2me | solution 1 for GlobalTheory.AdditiveSeries.addOf_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:43:36.794548+00:00
-- url     : https://prove2.me/submissions/e325435e-4587-4953-aae4-6d5963d33b7b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqZeroOfAdditiveOfPderiv
import Theorems.Thm_GlobalTheory_AdditiveSeries_gp_pair
import Theorems.Thm_GlobalTheory_AdditiveSeries_ev_pt_apply
import Theorems.Thm_GlobalTheory_AdditiveSeries_zero_addOf
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.AdditiveSeries
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.AdditiveSeries
theorem _root_.solution {n : ℕ} (G : FGLaw k d) {x : Pt k n d} (hx : GP x) : addOf G.F x 0 = x := by
  funext i
  have hz : GP (0 : Pt k n d) := gp_zero₂
  have h := congrArg (ev ![x, 0]) (G.comm i)
  rw [gt_ev_ev _ _ (gp_pair hx hz) (gp_pair (gp_pt 1) (gp_pt 0))] at h
  refine Eq.trans h.symm (Eq.trans ?_ (congrFun (zero_addOf G hx) i))
  unfold addOf
  congr 1
  funext j i
  fin_cases j <;> simp [ev_pt_apply (gp_pair hx hz)]
end GlobalTheory.AdditiveSeries
