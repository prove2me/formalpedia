-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLoc.compHom_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:30.989368+00:00
-- url     : https://prove2.me/submissions/18e0447a-fa0a-4fcf-9ba1-e2409e47c121

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLoc
namespace GlobalTheory.CompanionTheory.CotLoc
theorem _root_.solution (R R' P : Type) [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup P]
    [Module R' P] :
    letI := Module.compHom P (algebraMap R R')
    IsScalarTower R R' P :=
  letI := Module.compHom P (algebraMap R R')
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl
end GlobalTheory.CompanionTheory.CotLoc
