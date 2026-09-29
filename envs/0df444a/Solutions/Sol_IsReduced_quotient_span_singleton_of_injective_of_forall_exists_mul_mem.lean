-- Prove2me | solution 1 for IsReduced.quotient_span_singleton_of_injective_of_forall_exists_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2db46f38-57b1-5b89-8133-3902808e0ee8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsReduced_quotient_span_singleton_of_injective_of_forall_exists_mul_mem

theorem solution
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) (p : A)
    [IsReduced (B ⧸ Ideal.span {algebraMap A B p})]
    (S : Set A)
    (hS : ∀ b : B, ∃ s ∈ S, ∃ a : A, algebraMap A B a = algebraMap A B s * b)
    (htf : ∀ s ∈ S, ∀ a : A, s * a ∈ Ideal.span {p} → a ∈ Ideal.span {p}) :
    IsReduced (A ⧸ Ideal.span {p}) := by
  rw [← Ideal.isRadical_iff_quotient_reduced]
  intro a ⟨n, hn⟩

  have hB : (Ideal.Quotient.mk (Ideal.span {algebraMap A B p})) (algebraMap A B a) = 0 := by
    apply IsReduced.eq_zero
    refine ⟨n, ?_⟩
    rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, ← Set.image_singleton,
      ← Ideal.map_span]
    exact Ideal.mem_map_of_mem _ hn
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hB
  obtain ⟨b, hb⟩ := hB
  obtain ⟨s, hs, a', ha'⟩ := hS b

  have : algebraMap A B (s * a) = algebraMap A B (a' * p) := by
    rw [map_mul, map_mul, ← hb, ha']
    ring
  have hsa : s * a ∈ Ideal.span {p} := by
    rw [hinj this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  exact htf s hs a hsa

end S_IsReduced_quotient_span_singleton_of_injective_of_forall_exists_mul_mem
end P2MW
export P2MW.S_IsReduced_quotient_span_singleton_of_injective_of_forall_exists_mul_mem (solution)
