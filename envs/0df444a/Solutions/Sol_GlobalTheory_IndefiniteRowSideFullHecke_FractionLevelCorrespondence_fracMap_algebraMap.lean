-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence.fracMap_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:50:45.161583+00:00
-- url     : https://prove2.me/submissions/ccc26cd3-e0d4-4d30-b818-6aaacd843384

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_UniformTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TateUniformizationInput
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FractionLevelCorrespondence

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput
variable {O' R : Type} [CommRing O'] [IsDomain O'] [CommRing R] [IsDomain R]
namespace GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence
theorem _root_.solution (f : O' →+* R) (hf : Function.Injective f) (a : O') :
    fracMap f hf (algebraMap O' _ a) = algebraMap R _ (f a) :=
  IsFractionRing.lift_algebraMap _ a
end GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence
