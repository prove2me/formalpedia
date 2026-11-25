-- Prove2me | solution 1 for GlobalTheory.ActionGauge.logAd_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:45.104802+00:00
-- url     : https://prove2.me/submissions/e83e9886-7993-4c92-9e54-3fcefe6ffe26

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
theorem _root_.solution (h1 : B.ph1 = 1) (h2 : B.ph2 = 1) (a b : O) :
    logAd B (a + b) = logAd B a + logAd B b := by
  refine expS_inj (logAd_const B _) (by rw [map_add, logAd_const, logAd_const, add_zero]) ?_
  rw [gt_expS_add _ _ (logAd_const B a) (logAd_const B b), expS_logAd, expS_logAd, expS_logAd]
  have h := B.ad_add a b
  rwa [h1, h2, ev_one, ev_one, one_mul, mul_one] at h
end GlobalTheory.ActionGauge
