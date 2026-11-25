-- Prove2me | solution 1 for GlobalTheory.JetSer.IntTrans.related_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:14:24.696996+00:00
-- url     : https://prove2.me/submissions/72f70166-8a0d-47cf-b340-0aa637169b8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_map_ev1
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_map_ev2
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_map_ev3
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_mapPoint_pt
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_mapPoint_zero
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_mapPoint_comp1
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_mapPoint_addOf
import Theorems.Thm_P2M_GlobalTheory_JetSer_IntTrans_constantCoeff_map_eq_zero__741a16259184
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
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
variable {R k : Type} [CommRing R] [CommRing k] (f : R →+* k) {d : ℕ}
namespace GlobalTheory.JetSer.IntTrans
theorem _root_.solution {O : Type} [CommRing O] [StarRing O] {B B' : FB R d O} {φ φi : Pt R 1 d} {ε : PS R 2 d}
    (h : Related B B' φ φi ε) {C C' : FB k d O}
    (hF : C.G.F = mP f B.G.F) (hA : ∀ a, C.A.act a = mP f (B.A.act a))
    (h1 : C.ph1 = MvPowerSeries.map f B.ph1) (h2 : C.ph2 = MvPowerSeries.map f B.ph2)
    (hs : C.sy = MvPowerSeries.map f B.sy) (hd : ∀ a, C.ad a = MvPowerSeries.map f (B.ad a))
    (hF' : C'.G.F = mP f B'.G.F) (hA' : ∀ a, C'.A.act a = mP f (B'.A.act a))
    (h1' : C'.ph1 = MvPowerSeries.map f B'.ph1) (h2' : C'.ph2 = MvPowerSeries.map f B'.ph2)
    (hs' : C'.sy = MvPowerSeries.map f B'.sy) (hd' : ∀ a, C'.ad a = MvPowerSeries.map f (B'.ad a)) :
    Related C C' (mP f φ) (mP f φi) (MvPowerSeries.map f ε) := by
  have hφ : GP φ := h.inv.1
  have hφi : GP φi := h.inv.2.1
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt R (n := n) d j) := fun j => gp_pt j
  have hc : ∀ {n : ℕ} (j : Fin n), GP (comp1 φ (pt R (n := n) d j)) := fun j => gp_comp1 φ _ hφ (hp j)
  have mc : ∀ {n : ℕ} (ψ : Pt R 1 d) (j : Fin n),
      mP f (comp1 ψ (pt R (n := n) d j)) = comp1 (mP f ψ) (pt k d j) := fun ψ j => by
    rw [mapPoint_comp1 f ψ (hp j), mapPoint_pt]
  have hBa : ∀ a, GP (B.A.act a) := B.A.const
  have hBa' : ∀ a, GP (B'.A.act a) := B'.A.const
  refine ⟨⟨constantCoeff_map_eq_zero₂ f hφ, constantCoeff_map_eq_zero₂ f hφi, ?_, ?_⟩, ?_, ?_, fun i => ?_, fun a => ?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [← mapPoint_comp1 f φ hφi, h.inv.2.2.1, mapPoint_pt]
  · rw [← mapPoint_comp1 f φi hφ, h.inv.2.2.2, mapPoint_pt]
  · have := congrArg (MvPowerSeries.map f) h.ax0
    rwa [map_ev2 f gp_zero₂ (hp 0), mapPoint_zero, mapPoint_pt, map_one] at this
  · have := congrArg (MvPowerSeries.map f) h.ax1
    rwa [map_ev2 f (hp 0) gp_zero₂, mapPoint_zero, mapPoint_pt, map_one] at this
  · have := congrArg (MvPowerSeries.map f) (h.law i)
    unfold transF at this ⊢
    rw [map_ev1 f (gp_addOf _ B.G.const _ _ (hc 0) (hc 1)), mapPoint_addOf f _ (hc 0) (hc 1), mc, mc] at this
    rw [hF', hF]
    exact this
  · rw [hA', hA, h.act a, mapPoint_comp1 f φi (gp_comp1 _ _ (hBa a) hφ), mapPoint_comp1 f _ hφ]
  · have := congrArg (MvPowerSeries.map f) h.ph1
    rw [map_mul, map_mul, map_mul, map_ev2 f (gp_addOf _ B'.G.const _ _ (hp 0) (hp 1)) (hp 2),
      map_ev3 f (hc 0) (hc 1) (hc 2), map_ev2 f (hp 0) (hp 2), map_ev2 f (hp 1) (hp 2),
      mapPoint_addOf f _ (hp 0) (hp 1), mc, mc, mc, mapPoint_pt, mapPoint_pt, mapPoint_pt] at this
    rw [hF', h1', h1]
    exact this
  · have := congrArg (MvPowerSeries.map f) h.ph2
    rw [map_mul, map_mul, map_mul, map_ev2 f (hp 0) (gp_addOf _ B'.G.const _ _ (hp 1) (hp 2)),
      map_ev3 f (hc 0) (hc 1) (hc 2), map_ev2 f (hp 0) (hp 1), map_ev2 f (hp 0) (hp 2),
      mapPoint_addOf f _ (hp 1) (hp 2), mc, mc, mc, mapPoint_pt, mapPoint_pt, mapPoint_pt] at this
    rw [hF', h2', h2]
    exact this
  · have := congrArg (MvPowerSeries.map f) h.sy
    rw [map_mul, map_mul, map_ev2 f (hc 0) (hc 1), map_ev2 f (hp 1) (hp 0), mc, mc, mapPoint_pt, mapPoint_pt] at this
    rw [hs', hs]
    exact this
  · have := congrArg (MvPowerSeries.map f) (h.ad a)
    rw [map_mul, map_mul, map_ev2 f (hc 0) (hc 1),
      map_ev2 f (hp 0) (gp_comp1 _ _ (hBa' _) (hp 1)),
      map_ev2 f (gp_comp1 _ _ (hBa' _) (hp 0)) (hp 1), mc, mc, mc, mc, mapPoint_pt, mapPoint_pt] at this
    rw [hd', hd, hA', hA']
    exact this
end GlobalTheory.JetSer.IntTrans
