-- Prove2me | solution 1 for Ideal.span_le_pow_of_forall_isIdempotentElem_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ab4f9ec5-d75a-5ef3-8ed2-8e6398c7625d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_span_le_pow_of_forall_isIdempotentElem_of_subset

set_option autoImplicit false
universe u

theorem solution
    {R : Type u} [CommRing R] (S : Set R) (hS : ∀ e ∈ S, IsIdempotentElem e)
    (𝔭 : Ideal R) (hS𝔭 : S ⊆ 𝔭) (n : ℕ) : Ideal.span S ≤ 𝔭 ^ n := by
  rcases n with _ | n
  · rw [pow_zero, Ideal.one_eq_top]; exact le_top
  · rw [Ideal.span_le]
    intro e he
    have h := Ideal.pow_mem_pow (hS𝔭 he) (n + 1)
    rwa [(hS e he).pow_succ_eq] at h

end S_Ideal_span_le_pow_of_forall_isIdempotentElem_of_subset
end P2MW
export P2MW.S_Ideal_span_le_pow_of_forall_isIdempotentElem_of_subset (solution)
