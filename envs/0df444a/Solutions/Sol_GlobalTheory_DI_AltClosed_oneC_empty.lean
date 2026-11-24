-- Prove2me | solution 1 for GlobalTheory.DI.AltClosed.oneC_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:08:16.358805+00:00
-- url     : https://prove2.me/submissions/3ef14f1b-8035-4096-bae6-6ef9e1f80cda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.AltClosed
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]
omit [LinearOrder ι]
namespace GlobalTheory.DI.AltClosed
theorem _root_.solution : (oneC : Finset ι → ExteriorAlgebra K V) ∅ = 0 := by
  simp [oneC]
end GlobalTheory.DI.AltClosed
