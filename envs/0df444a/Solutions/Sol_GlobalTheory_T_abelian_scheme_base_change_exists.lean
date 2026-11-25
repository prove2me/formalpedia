-- Prove2me | solution 1 for GlobalTheory.T.abelian_scheme_base_change_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:52.770212+00:00
-- url     : https://prove2.me/submissions/823ab879-c3b3-4be5-88ed-3f28d957a60a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AbelianSchemeBaseChangeExists
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AbelianSchemeBaseChangeExistsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_exists_abelianScheme_baseChange_ringHom


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
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (A' : Over (Sp R')) (_ : GrpObj A') (φ : A'.left ⟶ A.left), IsAbelianScheme A' ∧
      SmoothOfRelativeDimension g A'.hom ∧ IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.exists_abelianScheme_baseChange_ringHom | exact GlobalTheory.CompanionTheory.Axis.exists_abelianScheme_baseChange_ringHom | (intros; apply GlobalTheory.CompanionTheory.Axis.exists_abelianScheme_baseChange_ringHom <;> assumption)
end _root_.GlobalTheory.T
