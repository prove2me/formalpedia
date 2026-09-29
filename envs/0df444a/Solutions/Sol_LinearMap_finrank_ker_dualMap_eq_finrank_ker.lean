-- Prove2me | solution 1 for LinearMap.finrank_ker_dualMap_eq_finrank_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ae099f31-0272-56fc-8ba3-c36be94ad2d0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_finrank_ker_dualMap_eq_finrank_ker

set_option autoImplicit false
open Module

theorem solution
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V) :
    finrank K (LinearMap.ker f.dualMap) = finrank K (LinearMap.ker f) := by
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range f)
  have h2 := f.finrank_range_add_finrank_ker
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range]
  omega

end S_LinearMap_finrank_ker_dualMap_eq_finrank_ker
end P2MW
export P2MW.S_LinearMap_finrank_ker_dualMap_eq_finrank_ker (solution)
