-- Prove2me | solution 1 for GlobalTheory.exists_regauge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:01:49.087183+00:00
-- url     : https://prove2.me/submissions/ef0c2202-13ad-4e2f-be38-a300d33aa88e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvRegaugedSecondLawFamily
import Theorems.Thm_GlobalTheory_Regauge_ev_pt_two
import Theorems.Thm_GlobalTheory_Regauge_eq_mul_expS
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant


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
open GlobalTheory
open GlobalTheory.Regauge
namespace GlobalTheory
theorem _root_.solution : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O) (h : PS k 2 d), (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) → ∃ B' : FB k d O, B'.G.F = B.G.F ∧ B'.A.act = B.A.act ∧ B.ph1 = B'.ph1 * FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) ∧ B.ph2 = B'.ph2 * FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) ∧ B.sy = B'.sy * FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h) ∧ ∀ a : O, B.ad a = B'.ad a * FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) := by
  intro k _ _ d O _ _ B h ⟨h0, h1⟩
  have hc : constantCoeff h = 0 := by
    have := congrArg constantCoeff h0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have hcc : ∀ {n : ℕ} {a b : Pt k n d}, GP a → GP b → constantCoeff (ev ![a, b] h) = 0 :=
    fun ha hb => gt_const_ev _ (pair_points_zero_constant ha hb) h hc
  refine ⟨regauge B h h0 h1, rfl, rfl, ?_, ?_, ?_, fun a => ?_⟩
  · refine eq_mul_expS _ _ _ ?_ (by ring)
    simp (maxDischargeDepth := 4) only [map_sub, map_add, hcc, gp_pt, gp_add, add_zero, sub_zero]
  · refine eq_mul_expS _ _ _ ?_ (by ring)
    simp (maxDischargeDepth := 4) only [map_sub, map_add, hcc, gp_pt, gp_add, add_zero, sub_zero]
  · refine eq_mul_expS _ _ _ ?_ (by rw [ev_pt_two]; ring)
    simp (maxDischargeDepth := 4) only [map_sub, hcc, hc, gp_pt, sub_zero]
  · refine eq_mul_expS _ _ _ ?_ (by ring)
    simp (maxDischargeDepth := 4) only [map_sub, hcc, gp_pt, gp_act, sub_zero]
end GlobalTheory
