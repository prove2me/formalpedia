-- Prove2me | solution 1 for Module.length_quotient_le_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/bb902fe2-a171-53c4-ac13-be3a032b4337

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_length_quotient_le_of_ker_le

set_option autoImplicit false

theorem solution
    {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (K : Submodule R M) (f : M →ₗ[R] N) (h : LinearMap.ker f ≤ K) :
    Module.length R (M ⧸ K) ≤ Module.length R N := by
  have h1 : Module.length R (M ⧸ K) ≤ Module.length R (M ⧸ LinearMap.ker f) :=
    Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)
  have h2 : Module.length R (M ⧸ LinearMap.ker f) = Module.length R (LinearMap.range f) :=
    (f.quotKerEquivRange).length_eq
  have h3 : Module.length R (LinearMap.range f) ≤ Module.length R N :=
    Module.length_le_of_injective (LinearMap.range f).subtype Subtype.val_injective
  exact h1.trans (h2.le.trans h3)

end S_Module_length_quotient_le_of_ker_le
end P2MW
export P2MW.S_Module_length_quotient_le_of_ker_le (solution)
