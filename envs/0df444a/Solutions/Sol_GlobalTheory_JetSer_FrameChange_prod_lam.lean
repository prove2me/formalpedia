-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.prod_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:23:26.017797+00:00
-- url     : https://prove2.me/submissions/9c80fc28-4b86-4313-b244-d406d4ed5379

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
import Theorems.Thm_P2M_GlobalTheory_JetSer_FrameChange_lift_lam__1e26ca842b72

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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε)
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.FrameChange
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
variable {G}
namespace GlobalTheory.JetSer.FrameChange
theorem _root_.solution {T : Over S} (x y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k, h ((lift x y).left ≫ lamφ G k) ^ lamε k = lamV h x y := by
  simp only [lift_lamφ]
  rw [Fin.prod_univ_four]
  show h (x * y).left ^ (1 : ℤ) * h x.left ^ (-1 : ℤ) * h y.left ^ (-1 : ℤ) * h (1 : T ⟶ G).left ^ (1 : ℤ) = _
  simp only [zpow_neg, zpow_one, lamV]
end GlobalTheory.JetSer.FrameChange
