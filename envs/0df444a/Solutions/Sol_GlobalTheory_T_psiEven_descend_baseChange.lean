-- Prove2me | solution 1 for GlobalTheory.T.psiEven_descend_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:24:22.472451+00:00
-- url     : https://prove2.me/submissions/be422445-eae1-4e38-b6ef-e369c2c1e81c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PsiEvenDescendBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PsiEvenDescendBaseChangeStatement
import Theorems.Thm_GlobalTheory_PsiRing_psiEven_descend


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalFnsSt → ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D'.PsiEven → D.PsiEven := by
  first | exact @GlobalTheory.PsiRing.psiEven_descend | exact GlobalTheory.PsiRing.psiEven_descend | (intros; apply GlobalTheory.PsiRing.psiEven_descend <;> assumption)
end _root_.GlobalTheory.T
