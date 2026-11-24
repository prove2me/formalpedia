-- Prove2me | solution 1 for GlobalTheory.QuadDeriv.dof_additive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:37:14.123949+00:00
-- url     : https://prove2.me/submissions/664828f2-3c0b-4057-b5d8-8cebe8aa57c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Theorems.Thm_GlobalTheory_QuadDeriv_dy_add
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_subst_first_point
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_subst_second_point
import Theorems.Thm_GlobalTheory_QuadDeriv_dof_eq

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
theorem _root_.solution (F : Fin d → PS k 2 d) (hF : GP F)
    (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0) (v : Fin d → k) (f : PS k 1 d)
    (hf : ev ![F] f = ev (n := 2) ![pt k d 0] f + ev (n := 2) ![pt k d 1] f) :
    Dof F v f = C (lin v f) := by
  rw [dof_eq F hF hU, hf, dy_add, formalSecondPointDerivative_subst_first_point, formalSecondPointDerivative_subst_second_point, zero_add]
end GlobalTheory.QuadDeriv
