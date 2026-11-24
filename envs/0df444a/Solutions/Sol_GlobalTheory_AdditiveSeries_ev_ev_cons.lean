-- Prove2me | solution 1 for GlobalTheory.AdditiveSeries.ev_ev_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:43:38.992994+00:00
-- url     : https://prove2.me/submissions/9f780f98-6543-4991-b1b9-70383c3f1d5a

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev
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
theorem _root_.solution {l m n : ℕ} {V : Fin m → Pt k n d} (hV : ∀ j, GP (V j)) {x : Pt k m d}
    {y : Fin l → Pt k m d} (hx : GP x) (hy : ∀ j, GP (y j)) (g : PS k (l + 1) d) :
    ev V (ev (Fin.cons x y) g) =
      ev (Fin.cons (fun i => ev V (x i)) fun j i => ev V (y j i)) g := by
  rw [gt_ev_ev V _ hV (gp_cons hx hy)]
  congr 1
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp
end GlobalTheory.AdditiveSeries
