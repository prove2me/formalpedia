-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.exists_test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:41:40.562752+00:00
-- url     : https://prove2.me/submissions/a36193c4-ea65-438f-b0cb-e91454c9246a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt


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
theorem _root_.solution (hJ : JetAlgSt) {G : Over (Spec (CommRingCat.of R))} (x : Fam G (Fin d)) (N : ℕ) :
    ∃ t : Fin N → Fam G (Fin N × Fin d), ∀ i, Rep x (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d i) (t i) := by
  have H := fun i : Fin N => (hJ R (Fin N × Fin d)).2.2.2.2 (Fin d) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d i)
    (gp_pt i)
  choose ψ hψ using fun i m => (H i m).1
  exact ⟨fun i m => spMap (ψ i m) ≫ x m, fun i => ⟨gp_pt i, fun m => ⟨ψ i m, hψ i m, rfl⟩⟩⟩
end GlobalTheory.ChartBaseChange
