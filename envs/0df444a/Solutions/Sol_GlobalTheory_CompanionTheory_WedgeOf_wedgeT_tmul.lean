-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.wedgeT_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:26:02.324615+00:00
-- url     : https://prove2.me/submissions/93b7825b-767b-419f-af26-40fe61543c4e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
variable {R : Type} [CommRing R] (V : Type) [AddCommGroup V] [Module R V]
namespace GlobalTheory.CompanionTheory.WedgeOf
theorem _root_.solution (a b : V) : wedgeT (R := R) V (a ⊗ₜ b) = exteriorPower.ιMulti R 2 ![a, b] := rfl
end GlobalTheory.CompanionTheory.WedgeOf
