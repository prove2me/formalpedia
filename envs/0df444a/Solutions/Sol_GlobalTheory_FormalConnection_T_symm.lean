-- Prove2me | solution 1 for GlobalTheory.FormalConnection.T_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:59:02.672302+00:00
-- url     : https://prove2.me/submissions/4d0d9ecf-2d83-403a-a4be-4df632575eb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Theorems.Thm_GlobalTheory_FormalConnection_cc_d_jac
import Theorems.Thm_GlobalTheory_FormalConnection_kappa_symm
import Theorems.Thm_GlobalTheory_FormalConnection_T_eq
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_comm
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_comm


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
theorem _root_.solution (b i j : Fin d) :
    ∑ c, Jac G c b * pderiv k ((0 : Fin 1), c) (Jac G j i) = ∑ c, Jac G c i * pderiv k ((0 : Fin 1), c) (Jac G j b) := by
  rw [T_eq, T_eq]
  congr 1
  · simp only [Ar]
    rw [FormalLog.pderiv_comm]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [cc_d_jac, cc_d_jac, kappa_symm]
end GlobalTheory.FormalConnection
