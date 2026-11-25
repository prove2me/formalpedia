-- Prove2me | solution 1 for GlobalTheory.UU.UnitCob.chV_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:19:38.793291+00:00
-- url     : https://prove2.me/submissions/42b8cbf5-3ce3-42d1-8704-f93b61006c04

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitCoboundaryOfMulCocycleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CoeffMemOfPoints
import Theorems.Thm_GlobalTheory_IsCoaction_injective


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
open GlobalTheory.UU GlobalTheory.UU.RingPoint
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.UnitCob
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Y : Over S}
namespace GlobalTheory.UU.UnitCob
theorem _root_.solution {Z : Over S} {t t' : Z ⟶ splitTorus S X} (h : ∀ χ, (chV t χ).val = (chV t' χ).val) : t = t' :=
  (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun a => Units.ext (h a.toAdd))
end GlobalTheory.UU.UnitCob
