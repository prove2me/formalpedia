-- Prove2me | solution 1 for GlobalTheory.JetSer.IsMapOf.twoChart_rep_of_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:23:26.038648+00:00
-- url     : https://prove2.me/submissions/92641dbd-4f0d-41dc-90f8-f38887185744

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TwoChartAddOfPtPt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
namespace GlobalTheory.JetSer
namespace IsMapOf
theorem _root_.solution {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} {d : ℕ}
    {x x' : Fam G (Fin d)} {φ : Pt R 1 d} (h : IsMapOf x x' (𝟙 G) φ) {n : ℕ} {a : Pt R n d}
    {y : Fam G (Fin n × Fin d)} (hy : Rep x a y) : Rep x' (comp1 φ a) y := by
  simpa only [Category.comp_id] using h.2 n a y hy
end IsMapOf
end GlobalTheory.JetSer
