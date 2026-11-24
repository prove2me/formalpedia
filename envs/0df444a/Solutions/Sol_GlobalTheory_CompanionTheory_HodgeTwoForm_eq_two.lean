-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeTwoForm.eq_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:27:16.312822+00:00
-- url     : https://prove2.me/submissions/9d65385b-86e9-4410-8cc3-e13799a98848

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
variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {n : ℕ}
namespace GlobalTheory.CompanionTheory.HodgeTwoForm
theorem _root_.solution (v : Fin 2 → M) : v = ![v 0, v 1] := by
  ext i; fin_cases i <;> rfl
end GlobalTheory.CompanionTheory.HodgeTwoForm
