-- Prove2me | solution 1 for IsLocalRing.exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/999bf743-75db-5fbd-b85d-e33397a1364f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient

set_option autoImplicit false

theorem solution
    {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] (ϖ : A) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖ0 : ϖ ≠ 0)
    [IsDomain (A ⧸ Ideal.span {ϖ})] [IsDiscreteValuationRing (A ⧸ Ideal.span {ϖ})] :
    ∃ t : A, Ideal.ofList [ϖ, t] = IsLocalRing.maximalIdeal A ∧ RingTheory.Sequence.IsRegular A [ϖ, t] := by
  set I : Ideal A := Ideal.span {ϖ} with hI

  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.exists_irreducible (A ⧸ I)
  have humax : IsLocalRing.maximalIdeal (A ⧸ I) = Ideal.span {u} := hu.maximalIdeal_eq
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective u

  have hmk : ∀ x ∈ IsLocalRing.maximalIdeal A, Ideal.Quotient.mk I x ∈ IsLocalRing.maximalIdeal (A ⧸ I) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    rintro hunit
    obtain ⟨y, hy⟩ := hunit.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← (Ideal.Quotient.mk I).map_one, Ideal.Quotient.mk_eq_mk_iff_sub_mem, hI, Ideal.mem_span_singleton'] at hy
    obtain ⟨r, hr⟩ := hy

    have hmem : r * ϖ ∈ IsLocalRing.maximalIdeal A := Ideal.mul_mem_left _ _ hϖ
    have hu : IsUnit (x * y) := by
      rw [show x * y = 1 - (-(r * ϖ)) by linear_combination -hr]
      exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
        ((IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.maximalIdeal A).neg_mem hmem))
    exact hx (isUnit_of_mul_isUnit_left hu)
  have ht𝔪 : t ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro htu
    have : IsUnit (Ideal.Quotient.mk I t) := htu.map _
    exact hu.not_isUnit this
  refine ⟨t, ?_, ?_⟩
  ·
    apply le_antisymm
    · rw [Ideal.ofList, Ideal.span_le]
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hx
      rcases hx with rfl | rfl
      · exact hϖ
      · exact ht𝔪
    · intro x hx
      have hx' : Ideal.Quotient.mk I x ∈ Ideal.span {Ideal.Quotient.mk I t} := by
        rw [← humax]; exact hmk x hx
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hx'
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
      rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton'] at hs
      obtain ⟨r, hr⟩ := hs
      have hx_eq : x = (-r) * ϖ + s * t := by linear_combination hr
      rw [hx_eq]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  ·
    refine RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal A (fun r hr => ?_) ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hϖ
      · exact ht𝔪
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff]
    refine ⟨fun x y hxy => mul_left_cancel₀ hϖ0 (by simpa only [smul_eq_mul] using hxy), ?_, RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩
    ·
      have ht0 : Ideal.Quotient.mk I t ≠ 0 := hu.ne_zero
      rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
      intro x hx
      rw [Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
      obtain ⟨z, -, hz⟩ := hx
      have hq : Ideal.Quotient.mk I t * Ideal.Quotient.mk I x = 0 := by
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
        exact ⟨z, by rw [← smul_eq_mul, ← hz, smul_eq_mul]⟩
      have hx0 : Ideal.Quotient.mk I x = 0 := (mul_eq_zero.mp hq).resolve_left ht0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx0
      obtain ⟨w, hw⟩ := hx0
      exact ⟨w, trivial, by rw [smul_eq_mul, hw]⟩

end S_IsLocalRing_exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient
end P2MW
export P2MW.S_IsLocalRing_exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient (solution)
