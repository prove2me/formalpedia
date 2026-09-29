-- Prove2me | solution 1 for Ideal.exists_mem_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_eq_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6ca4c7b2-e322-569a-acdb-b863f6740b76

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_mem_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_eq_span_singleton

set_option autoImplicit false

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]
    (I : Ideal R) (π : S) (hI : I.map (algebraMap R S) = Ideal.span {π}) (hπ : π ∈ nonZeroDivisors S) :
    ∃ g ∈ I, I.map (algebraMap R S) = Ideal.span {algebraMap R S g} ∧ algebraMap R S g ∈ nonZeroDivisors S := by
  classical
  have hfg : (I.map (algebraMap R S)).FG := by rw [hI]; exact ⟨{π}, by simp⟩
  have hjac : IsLocalRing.maximalIdeal S ≤ Ideal.jacobson ⊥ := IsLocalRing.maximalIdeal_le_jacobson ⊥

  obtain ⟨g, hgI, hgm⟩ : ∃ g ∈ I, algebraMap R S g ∉ IsLocalRing.maximalIdeal S • I.map (algebraMap R S) := by
    by_contra h
    push_neg at h
    have hle : I.map (algebraMap R S) ≤ ⊥ ⊔ IsLocalRing.maximalIdeal S • I.map (algebraMap R S) := by
      rw [bot_sup_eq, Ideal.map, Ideal.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact h x hx
    have h0 : I.map (algebraMap R S) ≤ ⊥ := Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac hle
    have hπ0 : π ∈ (⊥ : Ideal S) := h0 (hI ▸ Ideal.mem_span_singleton_self π)
    rw [Ideal.mem_bot] at hπ0
    exact zero_notMem_nonZeroDivisors (hπ0 ▸ hπ)
  have hfgJ : algebraMap R S g ∈ I.map (algebraMap R S) := Ideal.mem_map_of_mem _ hgI

  have hfgJ' : algebraMap R S g ∈ Ideal.span {π} := hI ▸ hfgJ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hfgJ'
  have haunit : IsUnit a := by
    by_contra hna
    apply hgm
    rw [← ha, hI]
    exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal a).mpr hna) (Ideal.mem_span_singleton_self π)
  refine ⟨g, hgI, ?_, ?_⟩
  · rw [hI, ← ha]
    exact (Ideal.span_singleton_mul_left_unit haunit π).symm
  · rw [← ha]
    exact (nonZeroDivisors S).mul_mem haunit.mem_nonZeroDivisors hπ

end S_Ideal_exists_mem_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_eq_span_singleton
end P2MW
export P2MW.S_Ideal_exists_mem_and_map_eq_span_singleton_and_mem_nonZeroDivisors_of_map_eq_span_singleton (solution)
