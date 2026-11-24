-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeTwoForm.Lf_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:27:15.660615+00:00
-- url     : https://prove2.me/submissions/e5b5dd47-f964-474e-8048-635b4d4f0dc1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeTwoForm
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
namespace GlobalTheory.CompanionTheory.HodgeTwoForm
theorem _root_.solution (hP : Par F) (l : Module.Dual R (Glob1 F)) (T : C) (x : Glob1 F) :
    Lf hP l T (evForm F T x) = algebraMap R (F.obj T) (l x) :=
  (hP T).lift_eq _ x
end GlobalTheory.CompanionTheory.HodgeTwoForm
