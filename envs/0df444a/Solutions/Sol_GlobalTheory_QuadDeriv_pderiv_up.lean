-- Prove2me | solution 1 for GlobalTheory.QuadDeriv.pderiv_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:06:04.062707+00:00
-- url     : https://prove2.me/submissions/d5b642fc-2ca4-4222-99ca-e9b3097868a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_pt_ne
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_ev_eq_zero
import Theorems.Thm_GlobalTheory_QuadDeriv_hUp

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
theorem _root_.solution (a : Pt k 2 d) (i i' : Fin d) : pderiv k ((2 : Fin 3), i) (up a i') = 0 := by
  refine pderiv_ev_eq_zero _ hUp _ _ fun j l => ?_
  fin_cases j
  · exact pderiv_pt_ne (show (0 : Fin 3) ≠ 2 by decide) _ _
  · exact pderiv_pt_ne (show (1 : Fin 3) ≠ 2 by decide) _ _
end GlobalTheory.QuadDeriv
