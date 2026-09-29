-- Prove2me | solution 1 for Ideal.exists_map_mk_span_singleton_eq_span_of_not_mem_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5f01874b-7f36-5055-af35-1c4b0feb8567

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_map_mk_span_singleton_eq_span_of_not_mem_smul

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ} (g : Fin (n + 1) → R)
    (x : R) (hx : x ∈ Ideal.span (Set.range g))
    (hxm : x ∉ IsLocalRing.maximalIdeal R • Ideal.span (Set.range g)) :
    ∃ g' : Fin n → R ⧸ Ideal.span ({x} : Set R),
      (Ideal.span (Set.range g)).map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) = Ideal.span (Set.range g') := by
  classical
  set I : Ideal R := Ideal.span (Set.range g) with hI
  set mk := Ideal.Quotient.mk (Ideal.span ({x} : Set R)) with hmk

  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx

  have hunit : ∃ j, IsUnit (a j) := by
    by_contra hno
    push_neg at hno
    apply hxm
    rw [← ha]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).2 (hno i)) (Ideal.subset_span ⟨i, rfl⟩)
  obtain ⟨j, hj⟩ := hunit
  obtain ⟨u, hu⟩ := hj

  have hsplit : a j * g j + ∑ i : Fin n, a (j.succAbove i) * g (j.succAbove i) = x := by
    rw [← ha, Fin.sum_univ_succAbove _ j]
  refine ⟨fun i => mk (g (j.succAbove i)), le_antisymm ?_ ?_⟩
  · rw [Ideal.map_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases hij : i = j
    · subst hij

      have hx0 : mk x = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
      have e1 : mk (a i) * mk (g i) = -(∑ k : Fin n, mk (a (i.succAbove k)) * mk (g (i.succAbove k))) := by
        have := congrArg mk hsplit
        rw [map_add, map_mul, map_sum, hx0] at this
        simp only [map_mul] at this
        linear_combination this
      have e2 : mk (g i) = mk (↑u⁻¹ : R) * -(∑ k : Fin n, mk (a (i.succAbove k)) * mk (g (i.succAbove k))) := by
        rw [← e1, ← mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, one_mul]
      rw [e2]
      refine Ideal.mul_mem_left _ _ ((Ideal.neg_mem_iff _).2 (Ideal.sum_mem _ (fun k _ => ?_)))
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
      exact Ideal.subset_span ⟨k, rfl⟩
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j.succAbove k, rfl⟩)

end S_Ideal_exists_map_mk_span_singleton_eq_span_of_not_mem_smul
end P2MW
export P2MW.S_Ideal_exists_map_mk_span_singleton_eq_span_of_not_mem_smul (solution)
