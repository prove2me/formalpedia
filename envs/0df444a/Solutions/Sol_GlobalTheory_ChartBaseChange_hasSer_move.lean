-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.hasSer_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:37.041885+00:00
-- url     : https://prove2.me/submissions/4ff2ada7-ffd1-4920-b540-492af72d2651

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Theorems.Thm_GlobalTheory_ChartBaseChange_fnVal_comp
import Theorems.Thm_GlobalTheory_ChartBaseChange_fnVal_spec

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
theorem _root_.solution {a : Fin N → Pt R' n d} {Θ : ∀ m, JetR R (Fin N × Fin d) m →ₐ[R] JetR R' (Fin n × Fin d) m}
    (hΘ : IsMove a Θ) {X Y : Scheme.{0}} (q : X ⟶ Y)
    (r : ∀ m, Spec (CommRingCat.of (JetR R' (Fin n × Fin d) m)) ⟶ X)
    (p : ∀ m, Spec (CommRingCat.of (JetR R (Fin N × Fin d) m)) ⟶ Y)
    (h : ∀ m, r m ≫ q = (spMap (Θ m)).left ≫ p m) (U : Y.Opens) (f : Γ(Y, U)) (g : PS R N d)
    (hg : HasSer p U f g) :
    HasSer r (q ⁻¹ᵁ U) ((q.app U).hom f) (ev a (MvPowerSeries.map (algebraMap R R') g)) := by
  intro m
  have H := fnVal_spec (Θ m).toRingHom (p m) U f (hg m).1
  have e : r m ≫ q = Spec.map (CommRingCat.ofHom (Θ m).toRingHom) ≫ p m := h m
  rw [← e] at H
  refine ⟨H.1, ?_⟩
  rw [fnVal_comp, H.2, (hg m).2]
  exact hΘ m g
end GlobalTheory.ChartBaseChange
