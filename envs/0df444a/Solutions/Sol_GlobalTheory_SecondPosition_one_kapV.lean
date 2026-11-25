-- Prove2me | solution 1 for GlobalTheory.SecondPosition.one_kapV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:52:55.836914+00:00
-- url     : https://prove2.me/submissions/589fd946-b871-4dc3-bdda-dcb8544de0f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalNeZeroOfIsIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIntegralTensorLeftOfSmoothGrpObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiMulPsiOfAdditionFirstVariable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiMulPsiOfAdditionSecondVariable
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV


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
open GlobalTheory
open GlobalTheory.SecondPosition
open FirstSlot
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.SecondPosition
theorem _root_.solution (D : DegPre R) (a b : D.X) {T : Over (Spec (CommRingCat.of R))} {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (y : T ⟶ D.P.A) :
    kapV D a b z J 1 y = (val D.sym y.left z J)⁻¹ * rigV D z J ^ 2 * cubV D.cub z J (cT D T b) y y⁻¹ *
      (cubV D.cub z J (cT D T (a - b)) (cT D T b) y)⁻¹ := by
  have h := isCub_cubV D.cub (T := T) (z := z) (J := J) hJ
  rw [kapV, kap0]
  simp only [h.face₃, h.face₂, h.face, _root_.mul_one, _root_.one_mul]
  rfl
end GlobalTheory.SecondPosition
