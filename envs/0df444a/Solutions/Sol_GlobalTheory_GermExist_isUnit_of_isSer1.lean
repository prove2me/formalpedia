-- Prove2me | solution 1 for GlobalTheory.GermExist.isUnit_of_isSer1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:56:58.720848+00:00
-- url     : https://prove2.me/submissions/41fd5598-db61-4d0c-810a-959f83aed1b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TopLePreimageWchart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GermExist
namespace GlobalTheory.GermExist
theorem _root_.solution (hrep : RepSt) (hser : SerSt) {R : Type} [CommRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)} (hx : IsUnivChart G d x)
    {U : G.left.Opens} {f : Γ(G.left, U)} (hf : IsUnit f) {r : PS R 1 d} (h : IsSer1 x U f r) : IsUnit r := by
  obtain ⟨h1, -, h3, -⟩ := hrep R G d x hx (Fin 1 × Fin d)
  obtain ⟨y, hy, -⟩ := h1 (pt R (n := 1) d 0) (gp_pt 0)
  have hc := (h3 _ y hy).1
  have hs := h 1 _ y hy
  have e : ev (n := 1) ![pt R (n := 1) d 0] r = r := by
    have : (![pt R d 0] : Fin 1 → Pt R 1 d) = fun j => pt R d j := by
      funext j; fin_cases j; rfl
    rw [this]
    unfold ev
    exact congrFun MvPowerSeries.subst_self r
  rw [e] at hs
  obtain ⟨⟨τ, hτ⟩, -⟩ := hser R (Fin 1 × Fin d) G.left (fun m => (y m).left)
    (fun m => by rw [← Over.comp_left, hc m]) U (hs 0).1
  rw [(hτ f r).1 hs]
  exact hf.map τ
end GlobalTheory.GermExist
