-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.fnVal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:32.873252+00:00
-- url     : https://prove2.me/submissions/c4ba037e-1c48-491a-a398-e9d3c2fe413f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree

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
variable {A : Type} [CommRing A] {X Y : Scheme.{0}}
namespace GlobalTheory.JetSer.FrameChange
theorem _root_.solution (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(X, U)) :
    fnVal p U f = evH p U h f := by
  unfold fnVal
  rw [dif_pos h]
  rfl
end GlobalTheory.JetSer.FrameChange
