-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.eval_standard_points_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:10:47.511406+00:00
-- url     : https://prove2.me/submissions/ed4703ca-85a6-40c6-a8fb-82bb9f3e3a09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Theorems.Thm_GlobalTheory_ChartBaseChange_ev_pt

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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom)
open GlobalTheory.JetSer ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartBaseChange
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
variable {d n N : ℕ}
namespace GlobalTheory.ChartBaseChange
theorem _root_.solution (f : PS R 3 d) :
    ev (n := 3) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 0, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 1,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 2] f = f := by
  refine Eq.trans ?_ (ev_pt f)
  congr 1
  funext j; fin_cases j <;> rfl
end GlobalTheory.ChartBaseChange
