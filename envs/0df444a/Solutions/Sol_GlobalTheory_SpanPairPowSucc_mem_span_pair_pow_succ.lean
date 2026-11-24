-- Prove2me | solution 1 for GlobalTheory.SpanPairPowSucc.mem_span_pair_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:53:35.343801+00:00
-- url     : https://prove2.me/submissions/10c6daa9-844c-48ba-b6ad-d5da01ad2104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MemSpanPairPowSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpanPairPowSucc
namespace GlobalTheory.SpanPairPowSucc
theorem _root_.solution {R : Type} [inst : CommRing R] (p w : R) (k : ℕ) :
    ∀ x ∈ Ideal.span {p, w} ^ (k + (1 : ℕ)),
      ∃ (c : R), ∃ G ∈ Ideal.span {p, w} ^ k, x = w ^ (k + (1 : ℕ)) * c + p * G := by
  induction k with
  | zero =>
    intro x hx
    rw [zero_add, pow_one] at hx
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hx
    exact ⟨b, a, by simp, by ring⟩
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro y hy z hz
      obtain ⟨c, G, hG, rfl⟩ := ih y hy
      obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hz
      refine ⟨c * b, w ^ (k + 1) * c * a + G * (a * p + b * w), ?_, by ring⟩
      refine Ideal.add_mem _ ?_ ?_
      · have hw : w ∈ Ideal.span ({p, w} : Set R) := Ideal.subset_span (by simp)
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hw _))
      · rw [pow_succ]
        exact Ideal.mul_mem_mul hG hz
    · rintro _ _ ⟨c₁, G₁, hG₁, rfl⟩ ⟨c₂, G₂, hG₂, rfl⟩
      exact ⟨c₁ + c₂, G₁ + G₂, Ideal.add_mem _ hG₁ hG₂, by ring⟩
end GlobalTheory.SpanPairPowSucc
