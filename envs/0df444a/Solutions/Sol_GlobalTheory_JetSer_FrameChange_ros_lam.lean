-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.ros_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:23:27.82485+00:00
-- url     : https://prove2.me/submissions/4acf2b7f-a9ca-44c0-ad8a-801249403c72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_ros


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
variable [IsCommMonObj G]
namespace GlobalTheory.JetSer.FrameChange
theorem _root_.solution (f g : G ⟶ G) {T : Over S} (x y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U)
    (t : U) : t⁻¹ * lamV h x (y ≫ g) =
      ((∏ i, h ((lift x y).left ≫ rosatiφ G f g i) ^ rosatiε i) * t)⁻¹ * lamV h (x ≫ f) y := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.prod_ros]
  simp only [lamV]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.JetSer.FrameChange
