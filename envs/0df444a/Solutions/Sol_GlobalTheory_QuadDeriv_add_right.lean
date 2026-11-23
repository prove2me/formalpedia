-- Prove2me | solution 1 for GlobalTheory.QuadDeriv.add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:49:49.608712+00:00
-- url     : https://prove2.me/submissions/13b2d64b-7014-45e5-ae7e-d58a33a44451

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_pair_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add
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
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.QuadDeriv
variable {k : Type} [CommRing k] {d : ℕ}
variable (F : Fin d → PS k 2 d) (hF : GP F) (g : PS k 2 d)
include hF
namespace GlobalTheory.QuadDeriv
theorem _root_.solution
    (h : ev (n := 3) ![pt k d 0, pt k d 1] g + ev (n := 3) ![pt k d 0, pt k d 2] g =
      ev (n := 3) ![pt k d 0, addOf F (pt k d 1) (pt k d 2)] g)
    {n : ℕ} (a b c : Pt k n d) (ha : GP a) (hb : GP b) (hc : GP c) :
    ev ![a, addOf F b c] g = ev ![a, b] g + ev ![a, c] g := by
  have hV := triple_points_zero_constant ha hb hc
  have hp : ∀ j : Fin 3, GP (pt k d j) := gp_pt
  have e := congrArg (ev ![a, b, c]) h
  rw [gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (hp _)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (hp _)),
    gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (gp_addOf F hF _ _ (hp _) (hp _))), eval_pair_points, eval_pair_points, eval_pair_points,
    evP_addOf _ hV F _ _ (hp _) (hp _)] at e
  simp only [evP_pt _ hV] at e
  exact e.symm
end GlobalTheory.QuadDeriv
