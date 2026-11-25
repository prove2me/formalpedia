-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HypWedge.hyp2St
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:39:35.358852+00:00
-- url     : https://prove2.me/submissions/e01cc282-75cb-4376-a304-d3ed22fc1164

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_wedgeHyp_of

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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HypWedge
theorem _root_.solution : OneFormCohSt → TwoFormCohSt → H2FieldHypothesis := by
  intro h1 h2 R _ C _ F hF _ hproj hcl hs hW halt
  obtain ⟨mu, hmu, hmu2, hmu3⟩ := h1 R C F hF
  obtain ⟨nu, hnu, hnui, hnus⟩ := h2 R C F hF
  exact wedgeHyp_of hproj hcl hs hW halt mu hmu hmu2 hmu3 nu hnu hnui hnus
end GlobalTheory.CompanionTheory.HypWedge
