-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.exterior_map_iota_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:54.823823+00:00
-- url     : https://prove2.me/submissions/d33feca6-3445-47c6-b324-5bf66edb1096

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_iota_multi_two_eta

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
theorem _root_.solution (f : V →ₗ[R] W) (a b : V) : exteriorPower.map 2 f (i2 (R := R) a b) = i2 (f a) (f b) := by
  rw [exteriorPower.map_apply_ιMulti, iota_multi_two_eta]; rfl
end GlobalTheory.CompanionTheory.Hodge.LiftO
