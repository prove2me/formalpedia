-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.jet_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:23:14.961948+00:00
-- url     : https://prove2.me/submissions/12afd204-3582-4642-9ced-0dbaec8e1eb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_fnVal_unit

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
theorem _root_.solution {R : Type} [CommRing R] {κ : Type} [Finite κ] {X : Scheme.{0}}
    {p : ∀ m : ℕ, Spec (CommRingCat.of (JetR R κ m)) ⟶ X} {U : X.Opens} {f : Γ(X, U)ˣ} {g : MvPowerSeries κ R}
    (h : HasSer p U f.val g) (m : ℕ) : toJet m g = (uv (p m) U f).val :=
  (h m).2.symm.trans (fnVal_unit _ _ (h m).1 f)
end GlobalTheory.JetSer.FrameChange
