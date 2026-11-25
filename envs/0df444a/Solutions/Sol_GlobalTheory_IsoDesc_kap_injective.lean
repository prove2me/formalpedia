-- Prove2me | solution 1 for GlobalTheory.IsoDesc.kap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:11:51.316797+00:00
-- url     : https://prove2.me/submissions/45922183-9778-4ded-9eff-d068de673960

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends

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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.IsoDesc
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.IsoDesc
theorem _root_.solution (σ : Z ⟶ Y) [Flat σ] (z : Z) : Function.Injective (kap σ z) := by
  let _ := (σ.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (σ z)) (Z.presheaf.stalk z) := Flat.stalkMap σ z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (σ z)) (Z.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (σ.stalkMap z).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (σ z)) (Z.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Units.map_injective (FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (σ z)) (Z.presheaf.stalk z))
end GlobalTheory.IsoDesc
