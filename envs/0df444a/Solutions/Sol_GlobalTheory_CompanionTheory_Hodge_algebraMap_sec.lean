-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.algebraMap_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:15.983208+00:00
-- url     : https://prove2.me/submissions/eaff69b9-c000-4592-9849-286e13261321

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SteinOfBijective

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
theorem _root_.solution (s : X ⟶ Sp R) (U : X.Opens) (r : R) :
    algebraMap R (Sec s U) r = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := rfl
end GlobalTheory.CompanionTheory.Hodge
