-- Prove2me | solution 1 for GlobalTheory.EquivDesc.exists_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:06:06.141702+00:00
-- url     : https://prove2.me/submissions/eefe8c37-9ef8-4eb7-89f0-28d442fc14b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom

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
open GlobalTheory.UU TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.EquivDesc
variable {S : Scheme.{0}}
variable {G B H : Over S} [GrpObj G] [GrpObj B] [GrpObj H] {q : G ⟶ B} {i : H ⟶ G} [IsMonHom q] [IsMonHom i]
  {L : LB G.left} {a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])}
omit [GrpObj H] [IsMonHom i]
namespace GlobalTheory.EquivDesc
theorem _root_.solution (hk : IsPullback i (toUnit _) q η[B]) {T : Over S} (x x' : T ⟶ G) (e : x' ≫ q = x ≫ q) :
    ∃ t : T ⟶ H, x' = (t ≫ i) * x := by
  have w : (x' * x⁻¹) ≫ q = toUnit T ≫ η[B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
    rfl
  exact ⟨hk.lift _ _ w, by rw [hk.lift_fst, inv_mul_cancel_right]⟩
end GlobalTheory.EquivDesc
