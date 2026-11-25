-- Prove2me | solution 1 for GlobalTheory.T.exists_unique_constant_of_compatible_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:56:10.675782+00:00
-- url     : https://prove2.me/submissions/e081ec47-79d5-4af6-a232-f37dcc3d0ba3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUniqueConstantOfCompatibleFamily
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUniqueConstantOfCompatibleFamilyStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_existsUnique_const_of_trivSqZeroExt


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (M : Type) [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (F' : C ⥤ CommAlgCat.{0} (TrivSqZeroExt R M)) (_ : BC F F'),
    Stein F' → ∀ z : ∀ T : C, M ⊗[R] F.obj T,
      (∀ (T T' : C) (φ : T ⟶ T'), z T' = (mp F φ).toLinearMap.lTensor M (z T)) →
      ∃! m : M, ∀ T, z T = m ⊗ₜ[R] (1 : F.obj T) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.existsUnique_const_of_trivSqZeroExt | exact GlobalTheory.CompanionTheory.Axis.existsUnique_const_of_trivSqZeroExt | (intros; apply GlobalTheory.CompanionTheory.Axis.existsUnique_const_of_trivSqZeroExt <;> assumption)
end _root_.GlobalTheory.T
