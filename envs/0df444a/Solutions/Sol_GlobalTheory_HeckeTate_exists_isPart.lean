-- Prove2me | solution 1 for GlobalTheory.HeckeTate.exists_isPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:19:10.22784+00:00
-- url     : https://prove2.me/submissions/63455103-de5f-4ab0-8715-77b17ad108a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R]
namespace GlobalTheory.HeckeTate
theorem _root_.solution [IsDedekindDomain R] {P : Ideal R} (hP : P.IsMaximal) {N : R} (hN : N ≠ 0) :
    ∃ e, IsPart P N e := by
  have h0 : Ideal.span {N} ≠ (0 : Ideal R) := by simpa using hN
  obtain ⟨k, C, hC, hk⟩ := WfDvdMonoid.max_power_factor' (x := P) h0
    (fun h => hP.ne_top (Ideal.isUnit_iff.1 h))
  have hCP : P ⊔ C = ⊤ := by
    by_contra hne
    have := hP.eq_of_le hne le_sup_left
    exact hC (Ideal.dvd_iff_le.2 (this ▸ le_sup_right))
  have hCP' : P ^ (k + 1) ⊔ C = ⊤ := Ideal.pow_sup_eq_top hCP
  obtain ⟨x, hx, e, he, hxe⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hCP')
  have hx' : 1 - e = x := by rw [← hxe]; ring
  refine ⟨e, ?_, ?_, fun q hq hNq hne => ?_⟩
  · rw [← Ideal.mem_span_singleton, hk, hx', mul_comm e]
    exact Ideal.mul_mem_mul (Ideal.pow_le_pow_right (Nat.le_succ k) hx) he
  · rw [hx']; exact Ideal.pow_le_self (Nat.succ_ne_zero k) hx
  · have : P ^ k * C ≤ q := by rw [← hk]; simpa using hNq
    rcases hq.isPrime.mul_le.1 this with h | h
    · exact absurd (hP.eq_of_le hq.ne_top (Ideal.IsPrime.le_of_pow_le (hP := hq.isPrime) h)).symm hne
    · exact h he
end GlobalTheory.HeckeTate
