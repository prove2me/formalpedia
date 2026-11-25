-- Prove2me | solution 1 for GlobalTheory.ChartCmp.Regauge.isCanonGauge_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:53:25.761667+00:00
-- url     : https://prove2.me/submissions/b03fddfd-824d-44f0-81a4-83fd340e8ed3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsCanonicalGaugeSubBiadditive
import Theorems.Thm_GlobalTheory_ChartCmp_Regauge_eq_of_forall_jeq
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.Regauge
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace GlobalTheory.ChartCmp.Regauge
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h g : PS k 2 d), B.IsCanonGauge k h → (∀ m, Biadd m B k g) → B.IsCanonGauge k (h - g) := by
  intro R _ d O _ _ B k _ _ _ h g hc hg
  have hF : ∀ i, MvPowerSeries.constantCoeff (B.FK k i) = 0 := fun i => by
    simp [FB.FK, FGLaw.mapF, B.G.const]
  have hA : ∀ a, GP (B.actK k a) := fun a i => by simp [FB.actK, B.A.const]
  have gA : ∀ {n : ℕ} (i j : Fin n), GP (addOf (B.FK k) (pt k d i) (pt k d j)) :=
    fun i j => gp_addOf _ hF _ _ (gp_pt i) (gp_pt j)
  have gC : ∀ {n : ℕ} (a : O) (i : Fin n), GP (comp1 (B.actK k a) (pt k d i)) :=
    fun a i => gp_comp1 _ _ (hA a) (gp_pt i)
  have a0 := eq_of_forall_jeq fun m => (hg m).ax0
  have a1 := eq_of_forall_jeq fun m => (hg m).ax1
  have d1 := eq_of_forall_jeq fun m => (hg m).add1
  have d2 := eq_of_forall_jeq fun m => (hg m).add2
  have sy := eq_of_forall_jeq fun m => (hg m).sym
  have bal := fun a => eq_of_forall_jeq fun m => (hg m).bal a
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [gt_ev_sub _ (pair_points_zero_constant gp_zero₂ (gp_pt _)), hc.ax0, a0, sub_zero]
  · rw [gt_ev_sub _ (pair_points_zero_constant (gp_pt _) gp_zero₂), hc.ax1, a1, sub_zero]
  · rw [hc.ph1, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)),
      gt_ev_sub _ (pair_points_zero_constant (gA _ _) (gp_pt _)), d1]
    congr 1; ring
  · rw [hc.ph2, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)),
      gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gA _ _)), d2]
    congr 1; ring
  · rw [hc.sy, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), sy]
    congr 1; ring
  · rw [hc.ad a, gt_ev_sub _ (pair_points_zero_constant (gC _ _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gC _ _)), bal a]
    congr 1; ring
end GlobalTheory.ChartCmp.Regauge
