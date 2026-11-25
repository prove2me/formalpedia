-- Prove2me | solution 1 for GlobalTheory.GaugeBaseChange.isCanonGauge_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:23.682941+00:00
-- url     : https://prove2.me/submissions/07794763-13bd-4f45-971e-8a54f12439fe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeNabValBaseChange
import Theorems.Thm_GlobalTheory_GaugeBaseChange_map_ev_two
import Theorems.Thm_P2M_GlobalTheory_GaugeBaseChange_baseChange_zero__6485ee57f770
import Theorems.Thm_GlobalTheory_GaugeBaseChange_map_expS
import Theorems.Thm_GlobalTheory_GaugeBaseChange_map_map_alg
import Theorems.Thm_GlobalTheory_GaugeBaseChange_mapP_FK
import Theorems.Thm_GlobalTheory_GaugeBaseChange_baseChange_actK
import Theorems.Thm_GlobalTheory_GaugeBaseChange_gp_FK
import Theorems.Thm_GlobalTheory_GaugeBaseChange_gp_actK
import Theorems.Thm_GlobalTheory_GaugeBaseChange_const_of_axis
import Theorems.Thm_GlobalTheory_QuadDeriv_baseChange_addOf
import Theorems.Thm_GlobalTheory_QuadDeriv_baseChange_comp1
import Theorems.Thm_GlobalTheory_QuadDeriv_baseChange_pt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
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
open GlobalTheory GlobalTheory.GaugeBaseChange
open GlobalTheory.QuadDeriv
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
  {k k' : Type} [CommRing k] [Algebra R k] [CommRing k'] [Algebra R k'] (β : k →ₐ[R] k')
variable [Algebra ℚ k] [Algebra ℚ k']
namespace GlobalTheory.GaugeBaseChange
theorem _root_.solution {h : PS k 2 d} (H : B.IsCanonGauge k h) :
    B.IsCanonGauge k' (MvPowerSeries.map (β : k →+* k') h) := by
  have hc := const_of_axis H.ax0
  have c2 : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → constantCoeff (ev ![a, b] h) = 0 :=
    fun a b ha hb => gt_const_ev _ (pair_points_zero_constant ha hb) h hc
  have gA : ∀ {n : ℕ} (i j : Fin n), GP (addOf (B.FK k) (pt k d i) (pt k d j)) :=
    fun i j => gp_addOf _ (gp_FK B) _ _ (gp_pt i) (gp_pt j)
  have gC : ∀ {n : ℕ} (a : O) (i : Fin n), GP (comp1 (B.actK k a) (pt k d i)) :=
    fun a i => gp_comp1 _ _ (gp_actK B a) (gp_pt i)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ax0
    rwa [map_ev_two _ _ _ gp_zero₂ (gp_pt 0), baseChange_zero₂, baseChange_pt, map_zero] at this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ax1
    rwa [map_ev_two _ _ _ (gp_pt 0) gp_zero₂, baseChange_zero₂, baseChange_pt, map_zero] at this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ph1
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, map_add, c2 _ _ (gp_pt _) (gp_pt _), c2 _ _ (gp_pt _) (gp_pt _),
        c2 _ _ (gA _ _) (gp_pt _), add_zero, sub_zero]), map_sub, map_add,
      map_ev_two _ _ _ (gp_pt _) (gp_pt _), map_ev_two _ _ _ (gp_pt _) (gp_pt _),
      map_ev_two _ _ _ (gA _ _) (gp_pt _), baseChange_addOf _ _ _ _ (gp_pt _) (gp_pt _), mapP_FK] at this
    simpa only [baseChange_pt] using this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.ph2
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, map_add, c2 _ _ (gp_pt _) (gp_pt _), c2 _ _ (gp_pt _) (gp_pt _),
        c2 _ _ (gp_pt _) (gA _ _), add_zero, sub_zero]), map_sub, map_add,
      map_ev_two _ _ _ (gp_pt _) (gp_pt _), map_ev_two _ _ _ (gp_pt _) (gp_pt _),
      map_ev_two _ _ _ (gp_pt _) (gA _ _), baseChange_addOf _ _ _ _ (gp_pt _) (gp_pt _), mapP_FK] at this
    simpa only [baseChange_pt] using this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) H.sy
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, c2 _ _ (gp_pt _) (gp_pt _), hc, sub_zero]), map_sub,
      map_ev_two _ _ _ (gp_pt _) (gp_pt _)] at this
    simpa only [baseChange_pt] using this
  · have := congrArg (MvPowerSeries.map (β : k →+* k')) (H.ad a)
    rw [map_map_alg, map_expS _ _ (by
      rw [map_sub, c2 _ _ (gC _ _) (gp_pt _), c2 _ _ (gp_pt _) (gC _ _), sub_zero]), map_sub,
      map_ev_two _ _ _ (gC _ _) (gp_pt _), map_ev_two _ _ _ (gp_pt _) (gC _ _),
      baseChange_comp1 _ _ _ (gp_pt _), baseChange_comp1 _ _ _ (gp_pt _), baseChange_actK, baseChange_actK] at this
    simpa only [baseChange_pt] using this
end GlobalTheory.GaugeBaseChange
