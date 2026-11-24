-- Prove2me | solution 1 for GlobalTheory.AdditiveSeries.pderiv_ev_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:43:45.174175+00:00
-- url     : https://prove2.me/submissions/e23a4e13-1e67-487f-b305-7761b9bcb44f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqZeroOfAdditiveOfPderiv
import Theorems.Thm_GlobalTheory_AdditiveSeries_gp_cons
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_pderiv_subst__7084ce132710
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.AdditiveSeries
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.AdditiveSeries
theorem _root_.solution {m n : ℕ} {x : Pt k n d} {y : Fin m → Pt k n d} (hx : GP x)
    (hy : ∀ j, GP (y j)) (v : Fin n × Fin d) (hv : ∀ j i, pderiv k v (y j i) = 0)
    (g : PS k (m + 1) d) :
    pderiv k v (ev (Fin.cons x y) g) =
      ∑ l, ev (Fin.cons x y) (pderiv k ((0 : Fin (m + 1)), l) g) * pderiv k v (x l) := by
  unfold ev
  rw [FormalCalc.pderiv_subst'
    (fun p : Fin (m + 1) × Fin d => gp_cons hx hy p.1 p.2), Fintype.sum_prod_type,
    Fin.sum_univ_succ]
  simp [hv]
end GlobalTheory.AdditiveSeries
