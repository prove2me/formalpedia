-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.evH_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:29.179688+00:00
-- url     : https://prove2.me/submissions/b051cd13-1302-4390-a913-bb362fad8f17

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
theorem _root_.solution (p : Spec (CommRingCat.of A) ⟶ X) {U V : X.Opens} (hUV : U ≤ V) (h : ⊤ ≤ p ⁻¹ᵁ U) (h' : ⊤ ≤ p ⁻¹ᵁ V)
    (f : Γ(X, V)) : evH p U h ((X.presheaf.map (homOfLE hUV).op).hom f) = evH p V h' f := by
  unfold evH
  have := Scheme.Hom.map_appLE p h (homOfLE hUV).op
  simp only [RingHom.comp_apply]
  congr 1
  rw [← this]
  rfl
end GlobalTheory.JetSer.FrameChange
