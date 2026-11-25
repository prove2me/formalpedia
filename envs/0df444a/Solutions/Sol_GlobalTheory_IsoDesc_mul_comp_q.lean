-- Prove2me | solution 1 for GlobalTheory.IsoDesc.mul_comp_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:00:00.482323+00:00
-- url     : https://prove2.me/submissions/e89b43a8-4259-44b8-a5ef-bb4ad3c9c5bd

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
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] [Module.Free ℤ X] {G : Over S'} {B : Over S}
  [GrpObj G] [IsCommMonObj G] [ConnectedSpace G.left] [GrpObj B] [IsCommMonObj B] {Q : TQ G X} {P : CP G}
  {M' : CP Q.B} {M : CP B} {β : Q.B.left ⟶ B.left} {hβ : β ≫ B.hom = Q.B.hom ≫ f}
namespace GlobalTheory.IsoDesc
theorem _root_.solution {Z : Over S'} (t : Z ⟶ splitTorus S' X) (g : Z ⟶ G) : ((t ≫ Q.i) * g) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  rw [MonObj.mul_comp, Category.assoc, Q.isKernel.w, ← Category.assoc, toUnit_unique (t ≫ toUnit _) (toUnit _),
    ← Hom.one_def, _root_.one_mul]
end GlobalTheory.IsoDesc
