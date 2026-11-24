-- Prove2me | solution 1 for GlobalTheory.JetSer.IntTrans.canon_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:23:32.084647+00:00
-- url     : https://prove2.me/submissions/a823143e-8fa3-48f4-8577-891968bdbfa3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_FK_eq
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_actK_eq
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
theorem _root_.solution (hF : C.G.F = mP (algebraMap R k) B.G.F) (hA : ∀ a, C.A.act a = mP (algebraMap R k) (B.A.act a))
    (h1 : C.ph1 = MvPowerSeries.map (algebraMap R k) B.ph1) (h2 : C.ph2 = MvPowerSeries.map (algebraMap R k) B.ph2)
    (hs : C.sy = MvPowerSeries.map (algebraMap R k) B.sy)
    (hd : ∀ a, C.ad a = MvPowerSeries.map (algebraMap R k) (B.ad a)) (h : PS k 2 d) :
    C.IsCanonGauge k h ↔ B.IsCanonGauge k h := by
  have e1 : FB.toK k C.ph1 = FB.toK k B.ph1 := (gt_map_id _).trans h1
  have e2 : FB.toK k C.ph2 = FB.toK k B.ph2 := (gt_map_id _).trans h2
  have e3 : FB.toK k C.sy = FB.toK k B.sy := (gt_map_id _).trans hs
  have e4 : ∀ a, FB.toK k (C.ad a) = FB.toK k (B.ad a) := fun a => (gt_map_id _).trans (hd a)
  constructor
  · intro g
    refine ⟨g.ax0, g.ax1, ?_, ?_, ?_, fun a => ?_⟩
    · rw [← e1, ← FK_eq hF]; exact g.ph1
    · rw [← e2, ← FK_eq hF]; exact g.ph2
    · rw [← e3]; exact g.sy
    · rw [← e4, ← actK_eq hA, ← actK_eq hA]; exact g.ad a
  · intro g
    refine ⟨g.ax0, g.ax1, ?_, ?_, ?_, fun a => ?_⟩
    · rw [e1, FK_eq hF]; exact g.ph1
    · rw [e2, FK_eq hF]; exact g.ph2
    · rw [e3]; exact g.sy
    · rw [e4, actK_eq hA, actK_eq hA]; exact g.ad a
end GlobalTheory.JetSer.IntTrans
