-- Prove2me | solution 1 for GlobalTheory.teichmuller_dvd_of_dvd_natCast_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:00.635345+00:00
-- url     : https://prove2.me/submissions/02845b09-30c1-4124-a370-a6d3847b45b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TeichmullerDistinguishedRegularSequence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    [IsDomain O] [CharP O l] [PerfectRing O l] (x : O) (hx : x ≠ 0) (a : WittVector l O)
    (h : WittVector.teichmuller l x ∣ ((l : ℕ) : WittVector l O) * a) :
    WittVector.teichmuller l x ∣ a := by
  obtain ⟨b, hb⟩ := h
  have h0 : (((l : ℕ) : WittVector l O) * a).coeff 0 = 0 := by
    rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  rw [hb, WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero] at h0
  have hb0 : b.coeff 0 = 0 := (mul_eq_zero.mp h0).resolve_left hx
  rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero, Ideal.mem_span_singleton] at hb0
  obtain ⟨c, rfl⟩ := hb0
  have hl : ((l : ℕ) : WittVector l O) ≠ 0 := WittVector.p_nonzero l O
  refine ⟨c, mul_left_cancel₀ hl ?_⟩
  rw [hb]; ring
end GlobalTheory
