-- Prove2me | solution 1 for GlobalTheory.JetSer.IntTrans.intTrans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:04.158023+00:00
-- url     : https://prove2.me/submissions/a43d304e-61a5-483a-a02f-e656d355806a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_map_ev2
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_mapPoint_pt
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_mapPoint_comp1
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_related_map
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_core
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_canon_iff
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_nabVal_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt


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
namespace GlobalTheory.JetSer.IntTrans
theorem _root_.solution (hN : NabTransSt)
    (hBC : ∀ (R k : Type) [CommRing R] [CommRing k] (f : R →+* k) (d : ℕ) (O : Type) [CommRing O] [StarRing O]
      (B : FB R d O), ∃ B' : FB k d O, (∀ i, B'.G.F i = MvPowerSeries.map f (B.G.F i)) ∧
        (∀ a i, B'.A.act a i = MvPowerSeries.map f (B.A.act a i)) ∧ B'.ph1 = MvPowerSeries.map f B.ph1 ∧
        B'.ph2 = MvPowerSeries.map f B.ph2 ∧ B'.sy = MvPowerSeries.map f B.sy ∧
        ∀ a, B'.ad a = MvPowerSeries.map f (B.ad a)) : IntTransSt := by
  intro R _ d O _ _ B B' φ φi ε r k _ _ _ h hh
  obtain ⟨C, hF, hA, h1, h2, hs, hd⟩ := hBC R k (algebraMap R k) d O B
  obtain ⟨C', hF', hA', h1', h2', hs', hd'⟩ := hBC R k (algebraMap R k) d O B'
  have hF : C.G.F = mP (algebraMap R k) B.G.F := funext hF
  have hF' : C'.G.F = mP (algebraMap R k) B'.G.F := funext hF'
  have hA : ∀ a, C.A.act a = mP (algebraMap R k) (B.A.act a) := fun a => funext (hA a)
  have hA' : ∀ a, C'.A.act a = mP (algebraMap R k) (B'.A.act a) := fun a => funext (hA' a)
  have r' := related_map (algebraMap R k) r hF hA h1 h2 hs hd hF' hA' h1' h2' hs' hd'
  obtain ⟨h', hc, hv⟩ := core hN r' h ((canon_iff hF hA h1 h2 hs hd h).2 hh)
  refine ⟨h', (canon_iff hF' hA' h1' h2' hs' hd' h').1 hc, fun w0 m f f' hf Λ _ u P => ?_⟩
  have hd : dLin (mP (algebraMap R k) φ) = (dLin φ).map (algebraMap R k) := by
    ext i j
    simp [dLin, mP]
  rw [← nabVal_eq hF' hA', ← nabVal_eq hF hA, ← hd]
  refine hv w0 m f f' ?_ Λ u P
  rw [FB.toK, map_ev2 _ (gp_pt 0) (gp_comp1 _ _ (B'.A.const w0) (gp_pt 0)),
    mapPoint_comp1 _ _ (gp_pt 0), mapPoint_pt, ← hA'] at hf
  exact hf
end GlobalTheory.JetSer.IntTrans
