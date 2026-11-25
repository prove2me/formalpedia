-- Prove2me | solution 1 for GlobalTheory.NabCol.dofN_inCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:00:59.708456+00:00
-- url     : https://prove2.me/submissions/26bd8b8c-1f3e-43e8-9db1-32a6e9514f47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Theorems.Thm_GlobalTheory_NabCol_inColHom_apply
import Theorems.Thm_GlobalTheory_NabCol_inCol_C
import Theorems.Thm_GlobalTheory_NabCol_pderiv_inCol
import Theorems.Thm_GlobalTheory_NabCol_ev_axis

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
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.PowGerm
open GlobalTheory GlobalTheory.NabCol
variable {k : Type} [CommRing k] {d n : ℕ}
namespace GlobalTheory.NabCol
theorem _root_.solution (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (f : PS k 1 d) :
    DofN F b u (inCol b f) = inCol b (Dof F u f) := by
  unfold DofN Dof
  rw [← inColHom_apply b (∑ _, _), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_sum, pderiv_inCol, if_pos rfl, inColHom_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, inColHom_apply, inColHom_apply, inCol_C, ev_axis]
end GlobalTheory.NabCol
