-- Prove2me | solution 1 for GlobalTheory.ChartCmp.jRel_axes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:30:39.216519+00:00
-- url     : https://prove2.me/submissions/70b9dd16-0f84-4719-981e-b186f7867f33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Theorems.Thm_GlobalTheory_ChartCmp_Axes_jEq_ev
import Theorems.Thm_GlobalTheory_ChartCmp_Axes_jEq_one_of_idem
import Theorems.Thm_GlobalTheory_ChartCmp_Axes_vec3
import Theorems.Thm_GlobalTheory_ChartCmp_Axes_addOf_zero
import Theorems.Thm_GlobalTheory_ChartCmp_Axes_ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one
import Theorems.Thm_GlobalTheory_ChartCmp_Axes_ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_pair_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.ChartCmp.Axes
namespace GlobalTheory.ChartCmp
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (m : ℕ) (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d), JRel m B B' φ φi ε → MvPowerSeries.constantCoeff ε = 1 ∧ JEq m (ev (n := 1) ![0, pt R (n := 1) d 0] ε) 1 ∧ JEq m (ev (n := 1) ![pt R (n := 1) d 0, 0] ε) 1 := by
  intro R _ d O _ _ m B B' φ φi ε h
  have hφ : GP φ := h.inv.1
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt R (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt R n d) := gp_zero₂
  have hc : ∀ {n : ℕ} (j : Fin n), GP (comp1 φ (pt R (n := n) d j)) := fun j => gp_comp1 φ _ hφ (hp j)
  have h1 : JEq m (ev (n := 1) ![0, pt R (n := 1) d 0] ε) 1 := by
    have hV : ∀ j, GP (![(0 : Pt R 1 d), 0, pt R (n := 1) d 0] j) := triple_points_zero_constant hz hz (hp 0)
    have H := jEq_ev _ hV h.ph1
    rw [gt_ev_mul _ hV, gt_ev_mul _ hV, gt_ev_mul _ hV, ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one _ B'.cocycleLeft_zero_fst _ (hp 0), _root_.one_mul,
      gt_ev_ev' _ _ hV (pair_points_zero_constant (gp_addOf _ B'.G.const _ _ (hp 0) (hp 1)) (hp 2)),
      gt_ev_ev' _ _ hV (triple_points_zero_constant (hc 0) (hc 1) (hc 2)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)),
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 1) (hp 2)), vec3, eval_pair_points, eval_pair_points, eval_pair_points,
      evP_addOf _ hV _ _ _ (hp 0) (hp 1), evP_comp1 _ hV _ _ (hp 0), evP_comp1 _ hV _ _ (hp 1),
      evP_comp1 _ hV _ _ (hp 2), evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at H
    change JEq m (ev ![addOf B'.G.F 0 0, pt R (n := 1) d 0] ε)
      (ev ![comp1 φ 0, comp1 φ 0, comp1 φ (pt R (n := 1) d 0)] B.ph1 *
        (ev ![0, pt R (n := 1) d 0] ε * ev ![0, pt R (n := 1) d 0] ε)) at H
    rw [addOf_zero _ B'.G.const, gt_comp1_zero φ hφ, ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one _ B.cocycleLeft_zero_fst _ (hc 0), _root_.one_mul] at H
    refine jEq_one_of_idem ?_ H
    rw [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0))]
    exact h.unit
  have h2 : JEq m (ev (n := 1) ![pt R (n := 1) d 0, 0] ε) 1 := by
    have hV : ∀ j, GP (![pt R (n := 1) d 0, (0 : Pt R 1 d), 0] j) := triple_points_zero_constant (hp 0) hz hz
    have H := jEq_ev _ hV h.ph2
    rw [gt_ev_mul _ hV, gt_ev_mul _ hV, gt_ev_mul _ hV, ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one _ B'.cocycleRight_zero_thd _ (hp 0), _root_.one_mul,
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (gp_addOf _ B'.G.const _ _ (hp 1) (hp 2))),
      gt_ev_ev' _ _ hV (triple_points_zero_constant (hc 0) (hc 1) (hc 2)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 1)),
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)), vec3, eval_pair_points, eval_pair_points, eval_pair_points,
      evP_addOf _ hV _ _ _ (hp 1) (hp 2), evP_comp1 _ hV _ _ (hp 0), evP_comp1 _ hV _ _ (hp 1),
      evP_comp1 _ hV _ _ (hp 2), evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at H
    change JEq m (ev ![pt R (n := 1) d 0, addOf B'.G.F 0 0] ε)
      (ev ![comp1 φ (pt R (n := 1) d 0), comp1 φ 0, comp1 φ 0] B.ph2 *
        (ev ![pt R (n := 1) d 0, 0] ε * ev ![pt R (n := 1) d 0, 0] ε)) at H
    rw [addOf_zero _ B'.G.const, gt_comp1_zero φ hφ, ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one _ B.cocycleRight_zero_thd _ (hc 0), _root_.one_mul] at H
    refine jEq_one_of_idem ?_ H
    rw [gt_const_ev_eq _ (pair_points_zero_constant (hp 0) hz)]
    exact h.unit
  refine ⟨?_, h1, h2⟩
  have := h1 0 (by simp)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_one] at this
  exact this
end GlobalTheory.ChartCmp
