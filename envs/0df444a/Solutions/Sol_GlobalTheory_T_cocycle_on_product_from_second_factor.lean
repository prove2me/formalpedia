-- Prove2me | solution 1 for GlobalTheory.T.cocycle_on_product_from_second_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:43:41.093855+00:00
-- url     : https://prove2.me/submissions/79d8d545-3047-4b0d-b47e-0f9563a38ce6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleOnProductFromSecondFactor
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleOnProductFromSecondFactorStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_exists_pull_of_vanish_fst


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), USt F →
    ∀ f : Z1 (box F), (∀ (a a' b : C) (φ : a ⟶ a'), f.1 (a, b) (a', b) (φ, 𝟙 b) = 0) →
      ∃ y : Z1 F, (boxR F).pullbackOneCocycle y = f := by
  first | exact @GlobalTheory.CompanionTheory.Axis.exists_pull_of_vanish_fst | exact GlobalTheory.CompanionTheory.Axis.exists_pull_of_vanish_fst | (intros; apply GlobalTheory.CompanionTheory.Axis.exists_pull_of_vanish_fst <;> assumption)
end _root_.GlobalTheory.T
