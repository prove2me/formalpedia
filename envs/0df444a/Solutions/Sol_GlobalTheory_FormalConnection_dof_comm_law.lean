-- Prove2me | solution 1 for GlobalTheory.FormalConnection.dof_comm_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:26:13.506237+00:00
-- url     : https://prove2.me/submissions/79918d74-e0fe-4529-8c03-3351f1c609ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Theorems.Thm_GlobalTheory_FormalConnection_vf_zeroc
import Theorems.Thm_GlobalTheory_FormalConnection_vf_comm
import Theorems.Thm_GlobalTheory_FormalConnection_dof_vf
import Theorems.Thm_GlobalTheory_FormalConnection_co_bracket

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
theorem _root_.solution (u v : Fin d → k) (g : PS k 1 d) : Dof G.F u (Dof G.F v g) = Dof G.F v (Dof G.F u g) := by
  simp only [dof_vf]
  rw [← sub_eq_zero, vf_comm]
  have hb : (fun p => vf (co G u) (co G v p) - vf (co G v) (co G u p)) = fun _ => (0 : PS k 1 d) :=
    funext (co_bracket G u v)
  rw [hb, vf_zeroc]
end GlobalTheory.FormalConnection
