-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.wd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:13.420349+00:00
-- url     : https://prove2.me/submissions/8fddfd04-aa2b-4cf9-8842-068dcd24f0dd

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
variable {R V V' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [Module R V] [Module R V']
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (a b : V) : wd (R := R) a b = exteriorPower.ιMulti R 2 ![a, b] := rfl
end GlobalTheory.CompanionTheory.HodgeAlt
