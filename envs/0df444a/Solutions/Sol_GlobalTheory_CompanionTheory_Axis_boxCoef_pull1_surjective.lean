-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.boxCoef_pull1_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:08:16.749412+00:00
-- url     : https://prove2.me/submissions/8c567d5a-4717-4ffa-9dff-79dc5b4ab753

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparison
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_pull1_surjective_of_bijective
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_boxCoef_bijective

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
open CategoryTheory.Limits
variable {R : Type} [CommRing R] {A : Over (Sp R)} {P : Type} [SemilatticeInf P]
namespace GlobalTheory.CompanionTheory.Axis
theorem _root_.solution (S : Sys A.left P) : Function.Surjective (boxCoef S).pull1 :=
  pull1_surjective_of_bijective _ _ (boxCoef S) rfl (boxCoef_bijective S)
end GlobalTheory.CompanionTheory.Axis
