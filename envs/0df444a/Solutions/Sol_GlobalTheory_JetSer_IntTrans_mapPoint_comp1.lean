-- Prove2me | solution 1 for GlobalTheory.JetSer.IntTrans.mapPoint_comp1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:39.754472+00:00
-- url     : https://prove2.me/submissions/ed71d470-f508-446e-9464-9a8bfc4517d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_map_ev1

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.IntTrans
variable {R k : Type} [CommRing R] [CommRing k] (f : R →+* k) {d : ℕ}
namespace GlobalTheory.JetSer.IntTrans
theorem _root_.solution {n : ℕ} (φ : Pt R 1 d) {a : Pt R n d} (ha : GP a) :
    mP f (comp1 φ a) = comp1 (mP f φ) (mP f a) := funext fun i => map_ev1 f ha (φ i)
end GlobalTheory.JetSer.IntTrans
