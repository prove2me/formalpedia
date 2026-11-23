-- Prove2me | solution 1 for GlobalTheory.UnifPullRig.pt_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:26.701165+00:00
-- url     : https://prove2.me/submissions/1d120475-7ba2-4461-adef-e02862b887cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CompatAlongOfSquare

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.UnifPullRig
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S S' B B' T T' T₁ T₁' G G' A A' : Scheme.{0}}
namespace GlobalTheory.UnifPullRig
theorem _root_.solution {X Y Y' Z : Scheme.{0}} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Y'} {d : Y' ⟶ Z}
    (h : a ≫ b = c ≫ d) (x : X) : b (a x) = d (c x) :=
  congrArg (fun g => g x) h
end GlobalTheory.UnifPullRig
