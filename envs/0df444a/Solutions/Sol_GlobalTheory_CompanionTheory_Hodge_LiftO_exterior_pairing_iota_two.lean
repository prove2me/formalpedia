-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.exterior_pairing_iota_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:24:46.963831+00:00
-- url     : https://prove2.me/submissions/d6a5c328-eef5-40ad-8aa9-a32da188dd70

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
theorem _root_.solution (l u : V →ₗ[R] R) (a b : V) : pair2 l u (i2 a b) = l a * u b - u a * l b :=
  (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).trans (Matrix.det_fin_two _)
end GlobalTheory.CompanionTheory.Hodge.LiftO
