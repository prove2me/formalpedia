-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.exists_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:27:47.103612+00:00
-- url     : https://prove2.me/submissions/24cf588a-4121-4b2c-8cb8-a2b18624f729

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Theorems.Thm_GlobalTheory_ChartBaseChange_exists_isMove
import Theorems.Thm_GlobalTheory_ChartBaseChange_exists_test
import Theorems.Thm_GlobalTheory_ChartBaseChange_ev_map_pt
import Theorems.Thm_GlobalTheory_ChartBaseChange_rep_iff

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
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)
namespace GlobalTheory.ChartBaseChange
theorem _root_.solution (hJ : JetAlgSt) {x : Fam G (Fin d)} {x' : Fam G' (Fin d)}
    (hx' : ∀ m, push hπ (x' m) = spMap (jetCoeff R R' (Fin d) m) ≫ x m)
    (a : Fin N → Pt R' n d) (y : Fin N → Fam G' (Fin n × Fin d)) (hy : ∀ i, Rep x' (a i) (y i)) :
    ∃ (Θ : ∀ m, JetR R (Fin N × Fin d) m →ₐ[R] JetR R' (Fin n × Fin d) m) (t : Fin N → Fam G (Fin N × Fin d)),
      IsMove a Θ ∧ (∀ i, Rep x (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d i) (t i)) ∧
      ∀ i m, push hπ (y i m) = spMap (Θ m) ≫ t i m := by
  have ha : ∀ i, GP (a i) := fun i => (hy i).1
  obtain ⟨Θ, hΘ⟩ := exists_isMove (R := R) hJ a ha
  obtain ⟨t, ht⟩ := exists_test hJ x N
  refine ⟨Θ, t, hΘ, ht, fun i => (rep_iff hπ hJ hx' ha hΘ (ht i) (y i)).1 ?_⟩
  rw [ev_map_pt a ha]
  exact hy i
end GlobalTheory.ChartBaseChange
