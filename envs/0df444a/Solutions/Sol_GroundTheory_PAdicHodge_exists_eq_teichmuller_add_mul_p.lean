-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_eq_teichmuller_add_mul_p
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:49.280503+00:00
-- url     : https://prove2.me/submissions/ac01a304-8d48-416d-890f-9f3110c7fd1d

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
theorem _root_.solution (x : WittVector p A) :
    ∃ v : WittVector p A, x = teichmuller p (x.coeff 0) + v * p := by
  have : x - teichmuller p (x.coeff 0) ∈ Ideal.span {(p : WittVector p A)} := by
    rw [mem_span_p_iff_coeff_zero_eq_zero]
    have h := add_coeff_zero (x - teichmuller p (x.coeff 0)) (teichmuller p (x.coeff 0))
    rw [sub_add_cancel, teichmuller_coeff_zero] at h
    exact (eq_sub_of_add_eq h.symm).trans (sub_self _)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨v, by rw [hv]; ring⟩
end GroundTheory.PAdicHodge
