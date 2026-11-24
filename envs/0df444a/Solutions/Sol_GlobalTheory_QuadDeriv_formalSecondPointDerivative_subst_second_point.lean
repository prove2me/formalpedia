-- Prove2me | solution 1 for GlobalTheory.QuadDeriv.formalSecondPointDerivative_subst_second_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:21:53.11658+00:00
-- url     : https://prove2.me/submissions/9e36baf0-880b-4487-995d-687d58aeb6f2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Theorems.Thm_GlobalTheory_QuadDeriv_vec1
import Theorems.Thm_GlobalTheory_QuadDeriv_ev_zero_pts
import Theorems.Thm_GlobalTheory_QuadDeriv_hX0
import Theorems.Thm_GlobalTheory_QuadDeriv_dy_ev
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_second_coordinate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
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
open GlobalTheory GlobalTheory.QuadDeriv
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.QuadDeriv
theorem _root_.solution (v : Fin d → k) (f : PS k 1 d) :
    dy v (ev (n := 2) ![pt k d 1] f) = C (lin v f) := by
  rw [dy_ev v _ (single_point_zero_constant (gp_pt 1)), vec1, evP_pt _ hX0, lin, map_sum, Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ev_zero_pts _ (by intro j; fin_cases j; rfl), map_mul]
  congr 1
  exact formalSecondPointDerivative_second_coordinate v i
end GlobalTheory.QuadDeriv
