-- Prove2me | solution 1 for GlobalTheory.ChartTrans.axis_pderiv_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:20.475877+00:00
-- url     : https://prove2.me/submissions/f11c0087-3d22-446e-a906-e90e958659e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Theorems.Thm_GlobalTheory_ChartTrans_pderiv_ev
import Theorems.Thm_GlobalTheory_ChartTrans_ev_sum
import Theorems.Thm_GlobalTheory_ChartTrans_vec1
import Theorems.Thm_GlobalTheory_ChartTrans_ev_at_zero
import Theorems.Thm_GlobalTheory_ChartTrans_axis_GP
import Theorems.Thm_GlobalTheory_ChartTrans_pderiv_comp_pt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_pair_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant


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
open GlobalTheory GlobalTheory.ChartTrans
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.ChartTrans
theorem _root_.solution (φ : Pt k 1 d) (hφ : GP φ) (H : PS k 2 d) (i : Fin d) :
    ev (n := 1) ![pt k (n := 1) d 0, 0] (pderiv k ((1 : Fin 2), i)
      (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] H)) =
    ∑ l, C (dLin φ l i) *
      ev ![φ] (ev (n := 1) ![pt k (n := 1) d 0, 0] (pderiv k ((1 : Fin 2), l) H)) := by
  have hΦ : ∀ j, GP (![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] j) :=
    pair_points_zero_constant (gp_comp1 φ _ hφ (gp_pt 0)) (gp_comp1 φ _ hφ (gp_pt 1))
  have hK : ∀ K : PS k 2 d, ev (n := 1) ![pt k (n := 1) d 0, 0]
      (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] K) =
      ev ![φ] (ev (n := 1) ![pt k (n := 1) d 0, 0] K) := by
    intro K
    rw [gt_ev_ev' _ _ axis_GP hΦ, eval_pair_points, evP_comp1 _ axis_GP φ _ (gp_pt 0),
      evP_comp1 _ axis_GP φ _ (gp_pt 1), evP_pt _ axis_GP, evP_pt _ axis_GP,
      gt_ev_ev' _ _ (single_point_zero_constant hφ) axis_GP, eval_pair_points, evP_pt _ (single_point_zero_constant hφ), evP_zero _ (single_point_zero_constant hφ)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [gt_comp1_pt_right, gt_comp1_zero φ hφ]
  have hL : ∀ l, ev (n := 1) ![pt k (n := 1) d 0, 0]
      (ev ![pt k (n := 2) d 1] (pderiv k ((0 : Fin 1), i) (φ l))) = C (dLin φ l i) := by
    intro l
    rw [gt_ev_ev' _ _ axis_GP (single_point_zero_constant (gp_pt 1)), vec1, evP_pt _ axis_GP]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ev_at_zero, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
    simp [dLin]
  rw [pderiv_ev _ hΦ, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_comp_pt]
  simp only [one_ne_zero, if_false, if_true, mul_zero, Finset.sum_const_zero, zero_add]
  rw [ev_sum _ axis_GP]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [gt_ev_mul _ axis_GP, hK, hL, mul_comm]
end GlobalTheory.ChartTrans
