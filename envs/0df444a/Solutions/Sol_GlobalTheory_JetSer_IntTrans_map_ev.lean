-- Prove2me | solution 1 for GlobalTheory.JetSer.IntTrans.map_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:46.870815+00:00
-- url     : https://prove2.me/submissions/7beb4c49-fae5-4f8f-8423-173d787c7f98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.IntTrans
variable {R k : Type} [CommRing R] [CommRing k] (f : R →+* k) {d : ℕ}
namespace GlobalTheory.JetSer.IntTrans
theorem _root_.solution {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j, GP (a j)) (g : PS R m d) :
    MvPowerSeries.map f (ev a g) = ev (fun j => mP f (a j)) (MvPowerSeries.map f g) := by
  unfold ev
  rw [MvPowerSeries.map_subst (gt_hasSubst a ha)]
  rfl
end GlobalTheory.JetSer.IntTrans
