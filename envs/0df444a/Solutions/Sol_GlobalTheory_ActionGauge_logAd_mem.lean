-- Prove2me | solution 1 for GlobalTheory.ActionGauge.logAd_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:47.536358+00:00
-- url     : https://prove2.me/submissions/d4868cad-cdcd-435a-83d4-8c39583016c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsActionGauge
import Theorems.Thm_GlobalTheory_ActionGauge_expS_inj
import Theorems.Thm_GlobalTheory_ActionGauge_expS_ev_logAd
import Theorems.Thm_GlobalTheory_ActionGauge_ev_logAd_const
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eq_zero_of_exp_eq_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_triple_points_zero_constant


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
theorem _root_.solution (h1 : B.ph1 = 1) (h2 : B.ph2 = 1) (c : O) : logAd B c ∈ biadd B.G := by
  refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
    fun n a b b' ha hb hb' => ?_⟩
  · refine eq_zero_of_exp_eq_one (ev_logAd_const B c _ _ gp_zero₂ hb) ?_
    refine (expS_ev_logAd B c _ _ gp_zero₂ hb).trans ?_
    have h := congrArg (ev ![b]) (B.adjoint_zero_fst c)
    rw [ev_ev_two _ (single_point_zero_constant hb) _ _ gp_zero₂ (gp_pt 0), evP_zero _ (single_point_zero_constant hb),
      evP_pt _ (single_point_zero_constant hb), ev_one] at h
    exact h
  · refine eq_zero_of_exp_eq_one (ev_logAd_const B c _ _ ha gp_zero₂) ?_
    refine (expS_ev_logAd B c _ _ ha gp_zero₂).trans ?_
    have h := congrArg (ev ![a]) (B.adjoint_zero_snd c)
    rw [ev_ev_two _ (single_point_zero_constant ha) _ _ (gp_pt 0) gp_zero₂, evP_zero _ (single_point_zero_constant ha),
      evP_pt _ (single_point_zero_constant ha), ev_one] at h
    exact h
  · have hs := gp_addOf _ B.G.const _ _ ha ha'
    have hV := triple_points_zero_constant ha ha' hb
    refine expS_inj (ev_logAd_const B c _ _ hs hb)
      (by rw [map_add, ev_logAd_const B c _ _ ha hb, ev_logAd_const B c _ _ ha' hb, add_zero]) ?_
    rw [gt_expS_add _ _ (ev_logAd_const B c _ _ ha hb) (ev_logAd_const B c _ _ ha' hb),
      expS_ev_logAd B c _ _ hs hb, expS_ev_logAd B c _ _ ha hb, expS_ev_logAd B c _ _ ha' hb]
    have h := B.adjoint_compat_left c
    rw [h1, ev_one, ev_one, one_mul, mul_one] at h
    have h' := congrArg (ev ![a, a', b]) h
    rw [gt_ev_mul _ hV,
      ev_ev_two _ hV _ _ (gp_addOf _ B.G.const _ _ (gp_pt 0) (gp_pt 1)) (gp_pt 2),
      ev_ev_two _ hV _ _ (gp_pt 0) (gp_pt 2), ev_ev_two _ hV _ _ (gp_pt 1) (gp_pt 2),
      evP_addOf _ hV _ _ _ (gp_pt 0) (gp_pt 1), evP_pt _ hV, evP_pt _ hV,
      evP_pt _ hV] at h'
    exact h'
  · have hs := gp_addOf _ B.G.const _ _ hb hb'
    have hV := triple_points_zero_constant ha hb hb'
    refine expS_inj (ev_logAd_const B c _ _ ha hs)
      (by rw [map_add, ev_logAd_const B c _ _ ha hb, ev_logAd_const B c _ _ ha hb', add_zero]) ?_
    rw [gt_expS_add _ _ (ev_logAd_const B c _ _ ha hb) (ev_logAd_const B c _ _ ha hb'),
      expS_ev_logAd B c _ _ ha hs, expS_ev_logAd B c _ _ ha hb, expS_ev_logAd B c _ _ ha hb']
    have h := B.adjoint_compat_right c
    rw [h2, ev_one, ev_one, one_mul, mul_one] at h
    have h' := congrArg (ev ![a, b, b']) h
    rw [gt_ev_mul _ hV,
      ev_ev_two _ hV _ _ (gp_pt 0) (gp_addOf _ B.G.const _ _ (gp_pt 1) (gp_pt 2)),
      ev_ev_two _ hV _ _ (gp_pt 0) (gp_pt 1), ev_ev_two _ hV _ _ (gp_pt 0) (gp_pt 2),
      evP_addOf _ hV _ _ _ (gp_pt 1) (gp_pt 2), evP_pt _ hV, evP_pt _ hV,
      evP_pt _ hV] at h'
    exact h'
end GlobalTheory.ActionGauge
