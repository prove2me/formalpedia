-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OneFormCoh.oneFormCohSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:34:44.059843+00:00
-- url     : https://prove2.me/submissions/2557ef60-c4dd-46fe-8520-197e03690f87

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExtendedFormNaturality
import Theorems.Thm_GlobalTheory_CompanionTheory_OneFormCoh_main

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OneFormCoh
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.OneFormCoh
theorem _root_.solution : OneFormCohSt := by
  unfold MainStatements.Hodge.OneFormCohSt MainStatements.Hodge.AllF
  intro R _ C _ F hF
  exact GlobalTheory.CompanionTheory.OneFormCoh.main F hF
end GlobalTheory.CompanionTheory.OneFormCoh
