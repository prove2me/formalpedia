-- Prove2me | solution 1 for GlobalTheory.QuadDeriv.ev_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:47:51.893813+00:00
-- url     : https://prove2.me/submissions/164bb7dd-d059-4558-8551-ebcaba729f6b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_sum__4ef444666b63
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_hasSubst


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
theorem _root_.solution {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) {α : Type} (s : Finset α)
    (f : α → PS k m d) : ev V (∑ a ∈ s, f a) = ∑ a ∈ s, ev V (f a) :=
  GlobalTheory.FormalCalc.subst_sum' (gt_hasSubst V hV) s f
end GlobalTheory.QuadDeriv
