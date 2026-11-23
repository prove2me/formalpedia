-- Prove2me | solution 1 for GlobalTheory.UU.TorusCompat.of_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:14:38.280768+00:00
-- url     : https://prove2.me/submissions/ec230d6c-b3a0-4177-8169-c41b7c197815

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat

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
noncomputable section
open GlobalTheory GlobalTheory.UU
open SplitTorus (bcMap bcMap_hom)
variable {S S' S'' : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {G'' : Over S''} {G' : Over S'} {G : Over S}
namespace GlobalTheory.UU
namespace TorusCompat
theorem _root_.solution {H : Over S} (i : splitTorus S X ⟶ G) (φ : G ⟶ H) :
    TorusCompat (𝟙 S) φ.left i (i ≫ φ) := by
  rw [torusCompat_iff, bcMap_id, Category.id_comp, Over.comp_left]
end TorusCompat
end GlobalTheory.UU
