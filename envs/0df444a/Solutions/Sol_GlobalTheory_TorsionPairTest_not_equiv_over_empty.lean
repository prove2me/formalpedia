-- Prove2me | solution 1 for GlobalTheory.TorsionPairTest.not_equiv_over_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:38:19.29152+00:00
-- url     : https://prove2.me/submissions/ed5d7463-57d0-446f-80ee-ae26622e56c4

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
theorem _root_.solution {W : (Spec (CommRingCat.of InhTate.R)).Opens} (ψW : PsiOn InhTate.tatePre W) :
    ∃ (T : Over W.toScheme) (_ : IsEmpty T.left) (p p' : QkPtW InhTate.tatePre W ψW 2 T), ¬ QkPtW.Equiv p p' := by
  let T : Over W.toScheme := Over.mk (isInitialOfIsEmpty.to W.toScheme : (∅ : Scheme.{0}) ⟶ _)
  have hT : IsEmpty T.left := inferInstanceAs (IsEmpty (∅ : Scheme.{0}))
  refine ⟨T, hT, emptyPair ψW 2 T (0 : ℤ), emptyPair ψW 2 T (1 : ℤ), ?_⟩
  rintro ⟨z, hz, -⟩
  have key : ∀ w : ℤ, (1 : ℤ) ≠ (0 : ℤ) + 2 • w := fun w hw => by
    rw [two_nsmul] at hw
    omega
  exact key z hz
end GlobalTheory.TorsionPairTest
