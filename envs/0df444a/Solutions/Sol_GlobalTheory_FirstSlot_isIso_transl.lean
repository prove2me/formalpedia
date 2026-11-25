-- Prove2me | solution 1 for GlobalTheory.FirstSlot.isIso_transl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:59:08.429716+00:00
-- url     : https://prove2.me/submissions/a9e2fa71-d970-4725-97db-e2cde83dce73

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
import Theorems.Thm_GlobalTheory_FirstSlot_comp_cT

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
open GlobalTheory.FirstSlot
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.FirstSlot
theorem _root_.solution (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (χ : D.X) :
    IsIso (lift (fst T D.P.A) (snd T D.P.A * cT D (T ⊗ D.P.A) χ)) := by
  refine ⟨lift (fst T D.P.A) (snd T D.P.A * (cT D (T ⊗ D.P.A) χ)⁻¹), ?_, ?_⟩
  · ext
    · simp
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, lift_snd, comp_cT, mul_inv_cancel_right,
        Category.id_comp]
  · ext
    · simp
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, lift_snd, comp_cT, inv_mul_cancel_right, Category.id_comp]
end GlobalTheory.FirstSlot
