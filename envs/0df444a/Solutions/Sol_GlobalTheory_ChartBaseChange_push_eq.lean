-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.push_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:14.420055+00:00
-- url     : https://prove2.me/submissions/ca865d8e-ddf9-428e-8654-c43367254412

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
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)
  {A : Type} [CommRing A] [Algebra R A] [Algebra R' A] [IsScalarTower R R' A]
namespace GlobalTheory.ChartBaseChange
theorem _root_.solution (y : sp (R₀ := R') A ⟶ G') :
    push hπ y = (Over.homMk (𝟙 _) ((Category.id_comp _).trans sp_tower) :
      sp (R₀ := R) A ⟶ Over.mk ((sp (R₀ := R') A).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
      pushHom hπ (sp (R₀ := R') A) y := by
  apply Over.OverMorphism.ext
  exact (Category.id_comp _).symm
end GlobalTheory.ChartBaseChange
