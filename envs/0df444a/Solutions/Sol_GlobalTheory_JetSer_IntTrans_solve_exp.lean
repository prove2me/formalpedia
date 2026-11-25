-- Prove2me | solution 1 for GlobalTheory.JetSer.IntTrans.solve_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:04:42.210435+00:00
-- url     : https://prove2.me/submissions/e5c9c716-f455-4acc-a1e0-9fbbbb262168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_expS_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.IntTrans
variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}
namespace GlobalTheory.JetSer.IntTrans
theorem _root_.solution {n : ℕ} {x y a c : PS k n d} (ha : constantCoeff a = 0) (hc : constantCoeff c = 0)
    (h : x * FB.expS k c = y * FB.expS k a) : x = y * FB.expS k (a - c) := by
  have hn : constantCoeff (-c) = 0 := by rw [map_neg, hc, neg_zero]
  rw [sub_eq_add_neg, gt_expS_add _ _ ha hn, ← _root_.mul_assoc, ← h, _root_.mul_assoc, ← gt_expS_add _ _ hc hn,
    add_neg_cancel, expS_zero, _root_.mul_one]
end GlobalTheory.JetSer.IntTrans
