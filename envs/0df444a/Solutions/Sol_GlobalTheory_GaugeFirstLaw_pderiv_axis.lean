-- Prove2me | solution 1 for GlobalTheory.GaugeFirstLaw.pderiv_axis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:09:58.804015+00:00
-- url     : https://prove2.me/submissions/efa18bed-2db1-44e7-b91b-b69b760f89f1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGaugeFirstLaw
import Theorems.Thm_GlobalTheory_ChartTrans_pderiv_ev
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
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
open GlobalTheory GlobalTheory.GaugeFirstLaw
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.GaugeFirstLaw
theorem _root_.solution (h : PS k 2 d) (i : Fin d) :
    pderiv k ((0 : Fin 1), i) (ev (n := 1) ![pt k d 0, 0] h) =
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), i) h) := by
  rw [GlobalTheory.ChartTrans.pderiv_ev _ (pair_points_zero_constant (gp_pt 0) gp_zero₂), Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, map_zero, mul_zero,
    Finset.sum_const_zero, add_zero, pt]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [pderiv_X_of_ne (by simpa using hj), mul_zero]
  · simp
end GlobalTheory.GaugeFirstLaw
