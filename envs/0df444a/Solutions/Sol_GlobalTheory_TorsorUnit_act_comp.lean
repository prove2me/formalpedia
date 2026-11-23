-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.act_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:33.203514+00:00
-- url     : https://prove2.me/submissions/c20a695f-4e7f-4dde-99fe-14ed52a23388

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight

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
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorsorUnit
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {q : G ⟶ B} {i : splitTorus S X ⟶ G}
open SplitTorusPoints
namespace GlobalTheory.TorsorUnit
theorem _root_.solution [IsMonHom q] (hi : IsPullback i (toUnit _) q η[B]) {Z : Over S}
    (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) : ((t ≫ i) * g) ≫ q = g ≫ q := by
  have : (t ≫ i) ≫ q = 1 := by
    rw [Category.assoc, hi.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  rw [MonObj.mul_comp, this, _root_.one_mul]
end GlobalTheory.TorsorUnit
