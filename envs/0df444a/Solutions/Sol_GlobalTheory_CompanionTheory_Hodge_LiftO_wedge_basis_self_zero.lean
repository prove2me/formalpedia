-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.wedge_basis_self_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:23:23.001987+00:00
-- url     : https://prove2.me/submissions/8a8ad36f-e88d-4a72-bcd7-8582cfac0329

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R V W V' W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution (a : V) : b2 (R := R) a a = 0 :=
  (exteriorPower.ιMulti R 2 (M := V)).map_eq_zero_of_eq ![a, a] (i := 0) (j := 1) rfl (by decide)
end GlobalTheory.CompanionTheory.Hodge.LiftO
