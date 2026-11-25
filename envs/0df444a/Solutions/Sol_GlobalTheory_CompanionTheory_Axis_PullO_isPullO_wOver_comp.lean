-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.PullO.isPullO_wOver_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:45:22.340776+00:00
-- url     : https://prove2.me/submissions/d717208a-a37c-4ab5-aede-f395e988d801

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsPullOWOverComp
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_PullO_isPullO_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis GlobalTheory.CompanionTheory.Axis.PullO
namespace GlobalTheory.CompanionTheory.Axis.PullO
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X Y Z : Over (Sp R)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : HO1 Z.hom) (b : HO1 Y.hom) (c : HO1 X.hom), IsPullO (wOver g) a b → IsPullO (wOver f) b c →
    IsPullO (wOver (f ≫ g)) a c := by
  intro R _ X Y Z f g a b c hab hbc
  exact isPullO_comp (wOver g) (wOver f) (wOver (f ≫ g)) a b c hab hbc
end GlobalTheory.CompanionTheory.Axis.PullO
