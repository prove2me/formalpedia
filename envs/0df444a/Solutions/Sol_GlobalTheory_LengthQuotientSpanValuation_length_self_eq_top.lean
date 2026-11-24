-- Prove2me | solution 1 for GlobalTheory.LengthQuotientSpanValuation.length_self_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:40:08.897786+00:00
-- url     : https://prove2.me/submissions/4bcde7a9-002d-4f37-a279-67161f5655b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthSelfEqTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.LengthQuotientSpanValuation
open Module
variable {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace GlobalTheory.LengthQuotientSpanValuation
theorem _root_.solution : Module.length R R = ⊤ := by
  rw [← Ring.ord_zero, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero]
end GlobalTheory.LengthQuotientSpanValuation
