-- Prove2me | solution 1 for GlobalTheory.ChartAction.rep_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:10:44.781841+00:00
-- url     : https://prove2.me/submissions/da04fffd-7f47-4db7-be98-f115ca810a3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ActStOf

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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartAction
namespace GlobalTheory.ChartAction
theorem _root_.solution (hR : RepSt) {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ}
    {x : Fam G (Fin d)} (hx : IsUnivChart G d x) {κ : Type} [Finite κ] {a b : Fin d → MvPowerSeries κ R}
    {y z : Fam G κ} (ha : Rep x a y) (hb : Rep x b z) (h : y = z) : a = b := by
  subst h
  obtain ⟨-, h2, h3, -⟩ := hR R G d x hx κ
  exact (h2 y (h3 a y ha)).unique ha hb
end GlobalTheory.ChartAction
