-- Prove2me | solution 1 for GlobalTheory.DI.AltClosed.dtot_oneC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:15.99628+00:00
-- url     : https://prove2.me/submissions/222e33be-fceb-426a-85c8-cc60b1a35e34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle
import Theorems.Thm_GlobalTheory_DI_AltClosed_d_one
import Theorems.Thm_GlobalTheory_DI_AltClosed_delta_oneC

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
namespace GlobalTheory.DI.AltClosed
theorem _root_.solution (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) :
    Dtot d (oneC : Finset ι → ExteriorAlgebra K V) = 0 := by
  funext t
  simp only [Dtot, delta_oneC, zero_add, Pi.zero_apply]
  unfold oneC
  split_ifs <;> simp [d_one d hd]
end GlobalTheory.DI.AltClosed
