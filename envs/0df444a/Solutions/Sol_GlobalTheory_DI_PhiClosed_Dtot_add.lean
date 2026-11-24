-- Prove2me | solution 1 for GlobalTheory.DI.PhiClosed.Dtot_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:09:30.117092+00:00
-- url     : https://prove2.me/submissions/0dcc5894-93d7-4fdc-9422-74da249727d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FrobeniusSplittingClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.PhiClosed
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]
namespace GlobalTheory.DI.PhiClosed
theorem _root_.solution (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (a b : Finset ι → ExteriorAlgebra K V) :
    Dtot d (a + b) = Dtot d a + Dtot d b := by
  funext t
  simp only [Dtot, delta, Pi.add_apply, smul_add, Finset.sum_add_distrib, map_add]
  abel
end GlobalTheory.DI.PhiClosed
