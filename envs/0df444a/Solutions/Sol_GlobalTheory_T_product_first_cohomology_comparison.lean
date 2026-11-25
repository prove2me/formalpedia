-- Prove2me | solution 1 for GlobalTheory.T.product_first_cohomology_comparison
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:23:47.065567+00:00
-- url     : https://prove2.me/submissions/53e5354e-92d6-45c3-aae5-53f6016b0f77

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparison
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparisonStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_exists_boxSys


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (P : Type) [SemilatticeInf P] (S : Sys A.left P),
    ∃ (Q : Type) (_ : SemilatticeInf Q) (S' : Sys (A ⊗ A).left Q)
      (m : CoefMap (RingHom.id R) (box (OSys A.hom S)) (OSys (A ⊗ A).hom S')),
      Function.Surjective m.pull1 ∧
      (∀ x c, IsPullO (wOver (fst A A)) x c →
        (resSys _ S').pull1 c = m.pull1 ((boxL _).pull1 ((resSys _ S).pull1 x))) ∧
      (∀ x c, IsPullO (wOver (snd A A)) x c →
        (resSys _ S').pull1 c = m.pull1 ((boxR _).pull1 ((resSys _ S).pull1 x))) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.exists_boxSys | exact GlobalTheory.CompanionTheory.Axis.exists_boxSys | (intros; apply GlobalTheory.CompanionTheory.Axis.exists_boxSys <;> assumption)
end _root_.GlobalTheory.T
