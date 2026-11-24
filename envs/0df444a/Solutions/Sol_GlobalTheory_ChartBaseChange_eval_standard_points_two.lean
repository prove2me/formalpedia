-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.eval_standard_points_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:41:39.524716+00:00
-- url     : https://prove2.me/submissions/1f6488e9-24b7-4a7d-b5a8-b09609979a21

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
theorem _root_.solution (f : PS R 2 d) :
    ev (n := 2) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 0, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d 1] f = f := by
  refine Eq.trans ?_ (ev_pt f)
  congr 1
  funext j; fin_cases j <;> rfl
end GlobalTheory.ChartBaseChange
