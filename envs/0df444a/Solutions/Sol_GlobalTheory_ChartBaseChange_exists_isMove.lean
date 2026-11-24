-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.exists_isMove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:10:48.450858+00:00
-- url     : https://prove2.me/submissions/dd7f0b10-1279-45d0-962a-d3a25c9ee373

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Theorems.Thm_GlobalTheory_ChartBaseChange_jetCoeff_toJet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
theorem _root_.solution (hJ : JetAlgSt) (a : Fin N → Pt R' n d) (ha : ∀ i, GP (a i)) :
    ∃ Θ, IsMove (R := R) a Θ := by
  have H := (hJ R' (Fin n × Fin d)).2.2.2.2 (Fin N × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  choose ψ hψ using fun m => (H m).1
  refine ⟨fun m => ((ψ m).restrictScalars R).comp (jetCoeff R R' _ m), fun m g => ?_⟩
  show ψ m (jetCoeff R R' _ m _) = _
  rw [jetCoeff_toJet]
  exact (H m).2 _ (hψ m) _
end GlobalTheory.ChartBaseChange
