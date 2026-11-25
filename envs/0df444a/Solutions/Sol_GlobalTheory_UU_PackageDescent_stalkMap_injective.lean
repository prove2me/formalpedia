-- Prove2me | solution 1 for GlobalTheory.UU.PackageDescent.stalkMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:53:54.192938+00:00
-- url     : https://prove2.me/submissions/a5dc06f6-1519-4c43-b136-b2969577f267

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PackageDescent
variable {X X' Y Y' Z : Scheme.{0}} {K : Type} [Fintype K]
namespace GlobalTheory.UU.PackageDescent
theorem _root_.solution (r : Z ⟶ Y) [Flat r] (z : Z) : Function.Injective (r.stalkMap z).hom := by
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z)
end GlobalTheory.UU.PackageDescent
