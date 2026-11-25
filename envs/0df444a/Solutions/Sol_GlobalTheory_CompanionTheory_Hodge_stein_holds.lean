-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.stein_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:53:11.715186+00:00
-- url     : https://prove2.me/submissions/27c0cf1e-01f1-47d4-a480-eed3300cae4c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SteinOfBijective
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_stein_of_bijective
import Theorems.Thm_GlobalTheory_globalFns_holds


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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge
variable {R : Type} [CommRing R] {X : Scheme.{0}}
namespace GlobalTheory.CompanionTheory.Hodge
theorem _root_.solution : SteinSt := by
  unfold MainStatements.Hodge.SteinSt MainStatements.Hodge.AllAb
  intro R _ A _ g hA _
  exact stein_of_bijective A.hom (GlobalTheory.globalFns_holds (Sp R) A hA)
end GlobalTheory.CompanionTheory.Hodge
