-- Prove2me | solution 1 for GlobalTheory.T.isPullO_comp_block_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:09:58.389592+00:00
-- url     : https://prove2.me/submissions/576e431b-719a-4c50-acab-1a0eb937c350

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsPullOWOverComp
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsPullOWOverCompStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_PullO_isPullO_wOver_comp


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X Y Z : Over (Sp R)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : HO1 Z.hom) (b : HO1 Y.hom) (c : HO1 X.hom), IsPullO (wOver g) a b → IsPullO (wOver f) b c →
    IsPullO (wOver (f ≫ g)) a c := by
  first | exact @GlobalTheory.CompanionTheory.Axis.PullO.isPullO_wOver_comp | exact GlobalTheory.CompanionTheory.Axis.PullO.isPullO_wOver_comp | (intros; apply GlobalTheory.CompanionTheory.Axis.PullO.isPullO_wOver_comp <;> assumption)
end _root_.GlobalTheory.T
