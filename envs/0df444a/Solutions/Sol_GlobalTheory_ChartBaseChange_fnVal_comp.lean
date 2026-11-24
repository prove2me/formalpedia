-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.fnVal_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:10:49.403012+00:00
-- url     : https://prove2.me/submissions/9f463107-a9c1-46c2-b672-f5896d5067cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf

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
variable {A B : Type} [CommRing A] [CommRing B] {X Y : Scheme.{0}}
namespace GlobalTheory.ChartBaseChange
theorem _root_.solution (r : Spec (CommRingCat.of A) ⟶ X) (q : X ⟶ Y) (V : Y.Opens) (f : Γ(Y, V)) :
    fnVal r (q ⁻¹ᵁ V) ((q.app V).hom f) = fnVal (r ≫ q) V f := by
  unfold fnVal
  by_cases h : ⊤ ≤ r ⁻¹ᵁ (q ⁻¹ᵁ V)
  · have h' : ⊤ ≤ (r ≫ q) ⁻¹ᵁ V := h
    rw [dif_pos h, dif_pos h', Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ (r ≫ q) ⁻¹ᵁ V := h
    rw [dif_neg h, dif_neg h']
end GlobalTheory.ChartBaseChange
