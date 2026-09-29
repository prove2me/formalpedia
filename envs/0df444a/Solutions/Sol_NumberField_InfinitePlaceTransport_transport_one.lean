-- Prove2me | solution 1 for NumberField.InfinitePlaceTransport.transport_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/450b2669-bcd5-5a55-8ed9-769ea06f2c43

import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfinitePlaceTransport_transport_one

set_option autoImplicit false

theorem solution (E K : Type*) [Field E] [Field K] [Algebra E K]
    (w : NumberField.InfinitePlace K) (h : (1 : K ≃ₐ[E] K) • w = w) :
    NumberField.InfinitePlaceTransport.transport (1 : K ≃ₐ[E] K) h = RingEquiv.refl w.Completion := by
  apply RingEquiv.ext
  intro x
  rw [RingEquiv.refl_apply]
  refine NumberField.InfinitePlace.Completion.induction_on _ x
    (isClosed_eq (NumberField.InfinitePlaceTransport.continuous_transport (1 : K ≃ₐ[E] K) h) continuous_id)
    fun a => ?_
  change NumberField.InfinitePlaceTransport.transport (1 : K ≃ₐ[E] K) h (a : w.Completion) = (a : w.Completion)
  rw [NumberField.InfinitePlaceTransport.transport_coe]
  rfl

end S_NumberField_InfinitePlaceTransport_transport_one
end P2MW
export P2MW.S_NumberField_InfinitePlaceTransport_transport_one (solution)
