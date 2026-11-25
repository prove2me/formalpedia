-- Prove2me | solution 1 for GlobalTheory.T.psiScalars_relations_up_to_baseUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:08:03.298187+00:00
-- url     : https://prove2.me/submissions/98e19386-58b3-4f18-bcae-b742f2cedeb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiScalarsRelationsUpToBaseUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiScalarsRelationsUpToBaseUnitsStatement
import Theorems.Thm_GlobalTheory_PsiScalUnit_main


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
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → (D.TauBimult → ∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) ∧ (D.PsiEven → ∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) := by
  first | exact @GlobalTheory.PsiScalUnit.main | exact GlobalTheory.PsiScalUnit.main | (intros; apply GlobalTheory.PsiScalUnit.main <;> assumption)
end _root_.GlobalTheory.T
