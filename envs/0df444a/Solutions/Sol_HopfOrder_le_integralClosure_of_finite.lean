-- Prove2me | solution 1 for HopfOrder.le_integralClosure_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e5c8a3fc-c328-589d-b3e5-6b4d81cc2225

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfOrder_le_integralClosure_of_finite

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v w

open scoped TensorProduct

theorem solution
    {R : Type u} [CommRing R] {A : Type w} [CommRing A] [Algebra R A]
    (S : Subalgebra R A) [Module.Finite R S] : S ≤ integralClosure R A := by
  intro x hx
  rw [mem_integralClosure_iff]
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have h : IsIntegral R (⟨x, hx⟩ : S) := Algebra.IsIntegral.isIntegral _
  exact h.map S.val

end S_HopfOrder_le_integralClosure_of_finite
end P2MW
export P2MW.S_HopfOrder_le_integralClosure_of_finite (solution)
