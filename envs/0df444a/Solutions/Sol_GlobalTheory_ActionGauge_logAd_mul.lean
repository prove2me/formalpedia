-- Prove2me | solution 1 for GlobalTheory.ActionGauge.logAd_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:49.993435+00:00
-- url     : https://prove2.me/submissions/76a93fda-34b4-477e-a4a6-4eafb91361de

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsActionGauge
import Theorems.Thm_GlobalTheory_ActionGauge_expS_inj
import Theorems.Thm_GlobalTheory_ActionGauge_logAd_const
import Theorems.Thm_GlobalTheory_ActionGauge_expS_logAd
import Theorems.Thm_GlobalTheory_ActionGauge_expS_ev_logAd
import Theorems.Thm_GlobalTheory_ActionGauge_ev_logAd_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.ActionGauge
variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  (B : FB k d O)
namespace GlobalTheory.ActionGauge
theorem _root_.solution (a b : O) : logAd B (a * b) =
    ev ![comp1 (B.A.act b) (pt k (n := 2) d 0), pt k (n := 2) d 1] (logAd B a) +
      ev ![pt k (n := 2) d 0, comp1 (B.A.act (star a)) (pt k (n := 2) d 1)] (logAd B b) := by
  have hx : GP (comp1 (B.A.act b) (pt k (n := 2) d 0)) :=
    gp_comp1 _ _ (B.A.const b) (gp_pt 0)
  have hz : GP (comp1 (B.A.act (star a)) (pt k (n := 2) d 1)) :=
    gp_comp1 _ _ (B.A.const _) (gp_pt 1)
  have c1 := ev_logAd_const B a _ _ hx (gp_pt 1)
  have c2 := ev_logAd_const B b _ _ (gp_pt 0) hz
  refine expS_inj (logAd_const B _) (by rw [map_add, c1, c2, add_zero]) ?_
  rw [gt_expS_add _ _ c1 c2, expS_logAd, expS_ev_logAd B a _ _ hx (gp_pt 1),
    expS_ev_logAd B b _ _ (gp_pt 0) hz, B.ad_mul]
end GlobalTheory.ActionGauge
