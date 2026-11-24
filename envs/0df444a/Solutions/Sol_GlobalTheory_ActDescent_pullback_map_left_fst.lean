-- Prove2me | solution 1 for GlobalTheory.ActDescent.pullback_map_left_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:05.495799+00:00
-- url     : https://prove2.me/submissions/0dbe7403-0677-4392-8d72-ae993c84a322

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_OActDescendOfGenerators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ActDescent
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j]
omit [Flat j] [Surjective j]
namespace GlobalTheory.ActDescent
namespace _root_.GlobalTheory.ActDescent
theorem _root_.solution {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback j).map a).left ≫ pullback.fst Y.hom j = pullback.fst X.hom j ≫ a.left := by
  exact pullback.lift_fst _ _ _
end _root_.GlobalTheory.ActDescent
end GlobalTheory.ActDescent
