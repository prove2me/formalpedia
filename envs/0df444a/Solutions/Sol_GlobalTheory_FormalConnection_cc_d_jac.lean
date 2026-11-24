-- Prove2me | solution 1 for GlobalTheory.FormalConnection.cc_d_jac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:11:48.558658+00:00
-- url     : https://prove2.me/submissions/ae66dbc9-6262-40e7-b7d6-8e16854780be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_zero_right


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.FormalLog
open GlobalTheory GlobalTheory.FormalConnection
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
namespace GlobalTheory.FormalConnection
theorem _root_.solution (b c i : Fin d) : constantCoeff (pderiv k ((0 : Fin 1), b) (Jac G c i)) =
    coeff (Finsupp.single ((0 : Fin 2), b) 1 + Finsupp.single ((1 : Fin 2), i) 1) (G.F c) := by
  have e : (eXv d) ((0 : Fin 1), b) = ((0 : Fin 2), b) := rfl
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, Jac, coeff_ev_zero_right, coeff_pderiv]
  simp [e, Finsupp.embDomain_single]
end GlobalTheory.FormalConnection
