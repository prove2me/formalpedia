-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.evH_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:23:27.892882+00:00
-- url     : https://prove2.me/submissions/7bc2ad40-ec42-4e66-b684-9c9492fa0414

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
theorem _root_.solution (p : Spec (CommRingCat.of A) ⟶ Y) (q : Y ⟶ X) (V : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ (q ⁻¹ᵁ V))
    (h' : ⊤ ≤ (p ≫ q) ⁻¹ᵁ V) (f : Γ(X, V)) : evH p _ h ((q.app V).hom f) = evH (p ≫ q) V h' f := by
  unfold evH
  simp only [RingHom.comp_apply]
  congr 1
end GlobalTheory.JetSer.FrameChange
