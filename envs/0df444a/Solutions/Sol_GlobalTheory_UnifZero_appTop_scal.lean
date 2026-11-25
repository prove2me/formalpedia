-- Prove2me | solution 1 for GlobalTheory.UnifZero.appTop_scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:17:50.119265+00:00
-- url     : https://prove2.me/submissions/40b4391c-7dca-4f03-9202-a10af89c7e7e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.UnifZero
open GlobalTheory.ToricData
variable {X Y Y' : Scheme.{0}} {J J' J'' : Type} [Fintype J] [Fintype J'] [Fintype J'']
variable {A B : Type} [CommRing A] [CommRing B]
namespace GlobalTheory.UnifZero
theorem _root_.solution (f : Y' ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of A)) (r : A) :
    f.appTop.hom (scal p r) = scal (f ≫ p) r := by
  simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
end GlobalTheory.UnifZero
