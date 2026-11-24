-- Prove2me | solution 1 for GroundTheory.PAdicHodge.isUnit_of_isUnit_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:15.718336+00:00
-- url     : https://prove2.me/submissions/b374c3b5-5aa0-47d1-98df-35c90ff89d15

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [CommRing A] [CharP A p] [PerfectRing A p]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {v : WittVector p A} (h : IsUnit (v.coeff 0)) : IsUnit v := by
  obtain ⟨u, hu⟩ := h.exists_left_inv
  set t := teichmuller p u * v with ht
  have h0 : t - 1 ∈ Ideal.span {(p : WittVector p A)} := by
    rw [mem_span_p_iff_coeff_zero_eq_zero]
    have h := add_coeff_zero (t - 1) 1
    rw [sub_add_cancel, one_coeff_zero, ht, mul_coeff_zero, teichmuller_coeff_zero, hu] at h
    exact (eq_sub_of_add_eq h.symm).trans (sub_self _)
  have hj := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h0) 1
  rw [mul_one, sub_add_cancel] at hj
  exact isUnit_of_mul_isUnit_right hj
end GroundTheory.PAdicHodge
