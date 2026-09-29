-- Prove2me | solution 1 for NumberField.InfinitePlaceTransport.transport_eq_actRingEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/379228a5-778f-5aaf-871c-5243c8c4a26d

import Mathlib
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfinitePlaceTransport_transport_eq_actRingEquiv

set_option autoImplicit false

theorem solution (E K : Type*) [Field E] [Field K] [Algebra E K]
    (w : NumberField.InfinitePlace K) (σ : NumberField.InfPlaceDecomp.decomp E K w) (h : (σ : K ≃ₐ[E] K) • w = w) :
    NumberField.InfinitePlaceTransport.transport (σ : K ≃ₐ[E] K) h = NumberField.InfPlaceDecomp.actRingEquiv σ :=
  rfl

end S_NumberField_InfinitePlaceTransport_transport_eq_actRingEquiv
end P2MW
export P2MW.S_NumberField_InfinitePlaceTransport_transport_eq_actRingEquiv (solution)
