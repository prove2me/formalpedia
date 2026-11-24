-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.toJet_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:23:28.739896+00:00
-- url     : https://prove2.me/submissions/48db4b18-95f7-49c4-8d6e-d80b7d8ec781

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
namespace GlobalTheory.JetSer.FrameChange
theorem _root_.solution (hJ : JetAlgSt) {R : Type} [CommRing R] {κ : Type} [Finite κ] (m : ℕ) (f g : MvPowerSeries κ R) :
    toJet m (f * g) = toJet m f * toJet m g := by
  obtain ⟨τ, hτ, -⟩ := (hJ R κ).1 m
  rw [← hτ, ← hτ, ← hτ, map_mul]
end GlobalTheory.JetSer.FrameChange
