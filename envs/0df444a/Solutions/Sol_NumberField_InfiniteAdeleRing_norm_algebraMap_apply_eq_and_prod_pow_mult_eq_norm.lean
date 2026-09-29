-- Prove2me | solution 1 for NumberField.InfiniteAdeleRing.norm_algebraMap_apply_eq_and_prod_pow_mult_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c7ca7953-2147-54e3-b9e6-51a67d83b688

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfiniteAdeleRing_norm_algebraMap_apply_eq_and_prod_pow_mult_eq_norm

set_option autoImplicit false

open NumberField

theorem solution
    (K : Type) [Field K] [NumberField K] (x : K) :
    (∀ v : InfinitePlace K, ‖algebraMap K (InfiniteAdeleRing K) x v‖ = v x) ∧
    ∏ v : InfinitePlace K, v x ^ v.mult = ‖algebraMap K (InfiniteAdeleRing K) x‖ := by
  have h : ∀ v : InfinitePlace K, ‖algebraMap K (InfiniteAdeleRing K) x v‖ = v x := by
    intro v
    rw [NumberField.InfiniteAdeleRing.algebraMap_apply]
    exact UniformSpace.Completion.norm_coe _
  refine ⟨h, ?_⟩
  rw [NumberField.InfiniteAdeleRing.norm_def]
  exact Finset.prod_congr rfl fun v _ => by rw [h v]

end S_NumberField_InfiniteAdeleRing_norm_algebraMap_apply_eq_and_prod_pow_mult_eq_norm
end P2MW
export P2MW.S_NumberField_InfiniteAdeleRing_norm_algebraMap_apply_eq_and_prod_pow_mult_eq_norm (solution)
