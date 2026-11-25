-- Prove2me | solution 1 for GlobalTheory.PsiInt.cT_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:34:23.728795+00:00
-- url     : https://prove2.me/submissions/5e7eb1df-043d-4fd4-a440-37314cc47e33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecRelationDefect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfSvalWhiskerRightEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_JKAppTopInjective

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
open GlobalTheory GlobalTheory.PsiInt
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.PsiInt
theorem _root_.solution (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h : D.c 0 = D.c 0 * D.c 0 := by
    have := D.c_add 0 0
    rwa [add_zero] at this
  have h1 : D.c 0 = 1 := left_eq_mul.1 h
  rw [cT, h1, MonObj.comp_one]
end GlobalTheory.PsiInt
