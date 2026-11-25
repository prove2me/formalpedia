-- Prove2me | solution 1 for GlobalTheory.QuadDeriv.dz_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:06:42.963915+00:00
-- url     : https://prove2.me/submissions/7effda4c-987c-41e3-ae95-7b1c4d10a98d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_pderiv_ev
import Theorems.Thm_GlobalTheory_QuadDeriv_hDown
import Theorems.Thm_P2M_GlobalTheory_QuadDeriv_constantCoeff_up_eq_zero__83ee02ec8fbc
import Theorems.Thm_GlobalTheory_QuadDeriv_down_up
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_up
import Theorems.Thm_GlobalTheory_QuadDeriv_sum_pt_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_pair_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_zero
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
open GlobalTheory GlobalTheory.QuadDeriv
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.QuadDeriv
theorem _root_.solution (g : PS k 2 d) (a : Pt k 2 d) (ha : GP a) (i : Fin d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), i) (ev ![up a, pt k d 2] g)) =
      ev ![a, 0] (pderiv k ((1 : Fin 2), i) g) := by
  rw [ev_pderiv_ev _ hDown _ (pair_points_zero_constant (constantCoeff_up_eq_zero₂ ha) (gp_pt 2)), Fin.sum_univ_two, eval_pair_points, down_up,
    evP_pt _ hDown]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_up, gt_ev_zero _ hDown, mul_zero,
    Finset.sum_const_zero, zero_add]
  rw [sum_pt_self _ hDown]
  rfl
end GlobalTheory.QuadDeriv
