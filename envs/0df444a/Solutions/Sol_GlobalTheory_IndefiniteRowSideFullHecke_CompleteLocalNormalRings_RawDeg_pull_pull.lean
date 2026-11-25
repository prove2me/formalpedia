-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg.pull_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:53:29.812747+00:00
-- url     : https://prove2.me/submissions/229ff7c1-b829-4391-ac1e-db4dbefdedcb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RawDegreeForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings
variable (R : Type) [CommRing R] [IsDomain R]
attribute [instance] RawDeg.addCommGroup RawDeg.free RawDeg.finite
open GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
variable {R} (D : RawDeg R)
namespace GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
theorem _root_.solution {Y Z Z' : Scheme.{0}} (f : Z ⟶ Y) (g : Z' ⟶ Z) (U : Y.Opens) (u : Γ(Y, U)ˣ) :
    pullU g _ (pullU f U u) = pullU (g ≫ f) U u := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
