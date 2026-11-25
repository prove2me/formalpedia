-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HypWedge.Nc_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:35.753739+00:00
-- url     : https://prove2.me/submissions/f6ad5b1c-41b0-4b63-b19a-dbfdd14dca1c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
import Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_characterExtensionRep_apply

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
theorem _root_.solution (hcl : Closed1 F = ⊤) (a b : Glob1 F) :
    Nc hcl (exteriorPower.ιMulti R 2 ![a, b]) = cupZZ F (cl hcl a) (cl hcl b) :=
  characterExtensionRep_apply _ _ a b
end GlobalTheory.CompanionTheory.HypWedge
