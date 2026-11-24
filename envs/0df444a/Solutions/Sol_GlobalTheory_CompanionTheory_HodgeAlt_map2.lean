-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.map2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:12.732328+00:00
-- url     : https://prove2.me/submissions/b8669055-a967-4b36-8589-2c5692e04f13

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R V V' W W' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [AddCommGroup W]
  [AddCommGroup W'] [Module R V] [Module R V'] [Module R W] [Module R W']
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (f : V →ₗ[R] V') (a b : V) :
    exteriorPower.map 2 f (exteriorPower.ιMulti R 2 ![a, b]) =
      exteriorPower.ιMulti R 2 ![f a, f b] := by
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i; fin_cases i <;> rfl
end GlobalTheory.CompanionTheory.HodgeAlt
