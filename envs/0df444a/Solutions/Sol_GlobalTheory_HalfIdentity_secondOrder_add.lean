-- Prove2me | solution 1 for GlobalTheory.HalfIdentity.secondOrder_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:12:47.367483+00:00
-- url     : https://prove2.me/submissions/f5743753-9f01-4f1c-b205-31330aae2150

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_SecondOrderMonomial

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.HalfIdentity
variable {k : Type} [CommRing k] {d : ℕ}
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)
variable [Fintype ι]
namespace GlobalTheory.HalfIdentity
theorem _root_.solution (c : ι → ι → k) (P Q : MvPolynomial ι k) :
    secondOrder k c (P + Q) = secondOrder k c P + secondOrder k c Q := by
  simp only [secondOrder, map_add, mul_add, Finset.sum_add_distrib]
end GlobalTheory.HalfIdentity
