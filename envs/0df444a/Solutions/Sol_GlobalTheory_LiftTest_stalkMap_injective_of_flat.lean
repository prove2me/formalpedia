-- Prove2me | solution 1 for GlobalTheory.LiftTest.stalkMap_injective_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:15.023893+00:00
-- url     : https://prove2.me/submissions/db4fb266-bd90-4b3c-9e29-1135c3daaff7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.LiftTest
namespace GlobalTheory.LiftTest
theorem _root_.solution {W Z : Scheme.{0}} (f : W ⟶ Z) [Flat f] (w : W) :
    Function.Injective (f.stalkMap w).hom := by
  have h := Flat.stalkMap f w
  algebraize [(f.stalkMap w).hom]
  have : IsLocalHom (algebraMap (Z.presheaf.stalk (f w)) (W.presheaf.stalk w)) := f.toLRSHom.prop w
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Z.presheaf.stalk (f w)) (B := W.presheaf.stalk w)
  exact FaithfulSMul.algebraMap_injective (Z.presheaf.stalk (f w)) (W.presheaf.stalk w)
end GlobalTheory.LiftTest
