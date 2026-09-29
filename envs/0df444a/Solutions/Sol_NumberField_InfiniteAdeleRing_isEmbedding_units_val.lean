-- Prove2me | solution 1 for NumberField.InfiniteAdeleRing.isEmbedding_units_val
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5e6c8189-8159-5e47-8bbe-73b1bd49f23d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfiniteAdeleRing_isEmbedding_units_val

set_option autoImplicit false

open NumberField

theorem solution
    (K : Type) [Field K] [NumberField K] :
    Topology.IsEmbedding (Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K)  := by

  refine Units.isEmbedding_val_mk' (f := fun x : InfiniteAdeleRing K => fun w : InfinitePlace K => (x w)⁻¹) ?_ ?_
  · refine continuousOn_pi.2 fun w => ?_
    have hc : ContinuousOn (fun x : InfiniteAdeleRing K => x w) {x : InfiniteAdeleRing K | IsUnit x} := (continuous_apply w).continuousOn
    refine ContinuousOn.inv₀ hc fun x hx => ?_
    obtain ⟨u, rfl⟩ := hx
    exact (u.map (Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w).toMonoidHom).ne_zero
  · intro u
    funext w
    have h := congrFun u.inv_mul w

    have h' : ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w * ((u : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w = 1 := h
    exact (eq_inv_of_mul_eq_one_left h').symm

end S_NumberField_InfiniteAdeleRing_isEmbedding_units_val
end P2MW
export P2MW.S_NumberField_InfiniteAdeleRing_isEmbedding_units_val (solution)
