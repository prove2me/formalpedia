-- Prove2me | solution 1 for GlobalTheory.TorsionPairTest.equiv_iff_of_isEmpty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:51.136773+00:00
-- url     : https://prove2.me/submissions/64f7e7f9-116d-4485-a1cf-f4ff39bb7f05

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UniformisationSurvey_EquivIffOfIsEmpty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionPairTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
variable {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) (k : ℕ) (T : Over W.toScheme) [IsEmpty T.left]
namespace GlobalTheory.TorsionPairTest
theorem _root_.solution (p p' : QkPtW D W ψW k T) :
    QkPtW.Equiv p p' ↔ ∃ z : D.X, p'.y = p.y + k • z :=
  ⟨fun ⟨z, hz, _⟩ => ⟨z, hz⟩, fun ⟨z, hz⟩ => ⟨z, hz, emptyPt D _,
    ⟨hom_eq _ _, fun _ => corr_of_isEmpty _ _ _ _ _ _ _⟩, hom_eq _ _, fun _ => corr_of_isEmpty _ _ _ _ _ _ _⟩⟩
end GlobalTheory.TorsionPairTest
