-- Prove2me | solution 1 for GlobalTheory.JetSer.IntTrans.actK_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:13:26.019769+00:00
-- url     : https://prove2.me/submissions/c42f0f1a-6fb7-4656-9d24-181e787aef97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_map_id


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
variable {R k : Type} [CommRing R] [CommRing k] [Algebra ℚ k] [Algebra R k] {d : ℕ}
  {O : Type} [CommRing O] [StarRing O] {B : FB R d O} {C : FB k d O}
namespace GlobalTheory.JetSer.IntTrans
theorem _root_.solution (hA : ∀ a, C.A.act a = mP (algebraMap R k) (B.A.act a)) (a : O) : C.actK k a = B.actK k a := by
  funext i
  exact (gt_map_id _).trans (congrFun (hA a) i)
end GlobalTheory.JetSer.IntTrans
