-- Prove2me | solution 1 for GlobalTheory.DI.AltClosed.d_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:08:14.730104+00:00
-- url     : https://prove2.me/submissions/0b8efa6c-f688-4b9f-89fd-61da34efd5e6

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
namespace GlobalTheory.DI.AltClosed
theorem _root_.solution (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) : d 1 = 0 := by
  have h1 := hd.mul 1 1
  simp only [mul_one, map_one, one_mul] at h1
  exact add_left_cancel (a := d 1) (by rw [add_zero]; exact h1.symm)
end GlobalTheory.DI.AltClosed
