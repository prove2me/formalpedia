-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLoc.opAct_central
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:27:02.375101+00:00
-- url     : https://prove2.me/submissions/3cb9286e-9ce3-4b15-a9d6-6eb3b6746d9e

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
theorem _root_.solution (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] :
    letI := opAct B M
    IsCentralScalar B M :=
  letI := opAct B M
  ⟨fun _ _ => rfl⟩
end GlobalTheory.CompanionTheory.CotLoc
