-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.ev_map_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:10:46.016283+00:00
-- url     : https://prove2.me/submissions/4defd3dc-113b-4c81-8f66-86a3dfff1eb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_X


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
theorem _root_.solution (a : Fin N → Pt R' n d) (ha : ∀ i, GP (a i)) (i : Fin N) :
    (fun j => ev a (MvPowerSeries.map (algebraMap R R') (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d i j))) = a i := by
  funext j
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt
  rw [MvPowerSeries.map_X, gt_ev_X a ha]
end GlobalTheory.ChartBaseChange
