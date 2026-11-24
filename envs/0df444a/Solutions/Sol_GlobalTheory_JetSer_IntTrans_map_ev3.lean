-- Prove2me | solution 1 for GlobalTheory.JetSer.IntTrans.map_ev3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:41:22.426796+00:00
-- url     : https://prove2.me/submissions/ac7e57b8-cdd6-46c8-955b-804aebdcb261

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_map_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_triple_points_zero_constant


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
theorem _root_.solution {n : ℕ} {a b c : Pt R n d} (ha : GP a) (hb : GP b) (hc : GP c) (g : PS R 3 d) :
    MvPowerSeries.map f (ev ![a, b, c] g) = ev ![mP f a, mP f b, mP f c] (MvPowerSeries.map f g) := by
  rw [map_ev f _ (triple_points_zero_constant ha hb hc)]
  congr 1
  funext j; fin_cases j <;> rfl
end GlobalTheory.JetSer.IntTrans
