-- Prove2me | solution 1 for GlobalTheory.ChartTrans.ev_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:49:33.593588+00:00
-- url     : https://prove2.me/submissions/8abb6a37-22ee-4b62-97dd-b96121ca7571

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Theorems.Thm_GlobalTheory_ChartTrans_ev_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul


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
open GlobalTheory GlobalTheory.ChartTrans
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.ChartTrans
theorem _root_.solution {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (r : k) (f : PS k m d) :
    ev V (C r * f) = C r * ev V f := by
  rw [gt_ev_mul V hV, ev_C]
end GlobalTheory.ChartTrans
