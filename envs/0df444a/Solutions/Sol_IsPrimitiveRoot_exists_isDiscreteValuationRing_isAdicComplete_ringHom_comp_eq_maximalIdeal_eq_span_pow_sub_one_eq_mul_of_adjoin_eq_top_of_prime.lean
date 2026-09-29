-- Prove2me | solution 1 for IsPrimitiveRoot.exists_isDiscreteValuationRing_isAdicComplete_ringHom_comp_eq_maximalIdeal_eq_span_pow_sub_one_eq_mul_of_adjoin_eq_top_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/5deaabf4-08d4-58e8-a708-2ab51016aef8

import Mathlib
import Theorems.Thm_IsPrimitiveRoot_exists_isDiscreteValuationRing_isAdicComplete_ringHom_comp_eq_maximalIdeal_eq_span_pow_sub_one_eq_mul_of_adjoin_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsPrimitiveRoot_exists_isDiscreteValuationRing_isAdicComplete_ringHom_comp_eq_maximalIdeal_eq_span_pow_sub_one_eq_mul_of_adjoin_eq_top_of_prime

theorem solution
    (q : ℕ) [Fact q.Prime]

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)})
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A₀ A]
    (hinj : Function.Injective (algebraMap A₀ A)) [Module.Finite A₀ A]
    (ζ : A) (hζ : IsPrimitiveRoot ζ q) (hadj : Algebra.adjoin A₀ {ζ} = ⊤)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] (hW₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {(q : W₀)})
    [Algebra A₀ W₀]

    (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] [Algebra W₀ R₀] [IsLocalHom (algebraMap W₀ R₀)]
    (σ₀ : A →+* R₀)
    (hσ₀ : ∀ a₀ : A₀, σ₀ (algebraMap A₀ A a₀) = algebraMap W₀ R₀ (algebraMap A₀ W₀ a₀)) :
    ∃ (W₁ : Type) (_ : CommRing W₁) (_ : IsDomain W₁) (_ : IsDiscreteValuationRing W₁)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁)
      (j₁ : W₀ →+* W₁) (σ : A →+* W₁) (ι₁ : W₁ →+* R₀) (_ : IsLocalHom ι₁),
      ι₁.comp j₁ = algebraMap W₀ R₀ ∧ ι₁.comp σ = σ₀ ∧
      (∀ a₀ : A₀, σ (algebraMap A₀ A a₀) = j₁ (algebraMap A₀ W₀ a₀)) ∧
      IsLocalRing.maximalIdeal W₁ = Ideal.span {σ ϖ} ∧
      ∃ ε₁ : W₁, IsUnit ε₁ ∧ (σ ϖ) ^ (q - 1) = ε₁ * (q : W₁) := by
  by_cases hq3 : 3 ≤ q
  · exact IsPrimitiveRoot.exists_isDiscreteValuationRing_isAdicComplete_ringHom_comp_eq_maximalIdeal_eq_span_pow_sub_one_eq_mul_of_adjoin_eq_top
      q hq3 A₀ hA₀q A hinj ζ hζ hadj ϖ hϖ W₀ hW₀ R₀ σ₀ hσ₀
  ·
    have hq2 : q = 2 := by
      have h2 := (Fact.out : q.Prime).two_le
      omega
    have hζ2 : IsPrimitiveRoot ζ 2 := by rw [← hq2]; exact hζ
    have hζ1 : ζ = -1 := hζ2.eq_neg_one_of_two_right

    have hsurj : Function.Surjective (algebraMap A₀ A) := by
      intro a
      have ha : a ∈ Algebra.adjoin A₀ ({ζ} : Set A) := by rw [hadj]; exact Algebra.mem_top
      have hle : Algebra.adjoin A₀ ({ζ} : Set A) ≤ ⊥ := by
        refine Algebra.adjoin_le ?_
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx, hζ1]
        exact neg_mem (one_mem _)
      exact Algebra.mem_bot.mp (hle ha)
    set e : A₀ ≃+* A := RingEquiv.ofBijective (algebraMap A₀ A) ⟨hinj, hsurj⟩ with he
    have heap : ∀ a₀ : A₀, e a₀ = algebraMap A₀ A a₀ := fun _ => rfl

    obtain ⟨p₀, hp₀⟩ := hsurj ϖ
    have hϖmem : ϖ ∈ IsLocalRing.maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
    have hp₀mem : p₀ ∈ IsLocalRing.maximalIdeal A₀ := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hϖu : IsUnit ϖ := by rw [← hp₀]; exact hu.map (algebraMap A₀ A)
      exact ((IsLocalRing.mem_maximalIdeal _).mp hϖmem) hϖu
    have hmax₀ : IsLocalRing.maximalIdeal A₀ = Ideal.span {p₀} := by
      refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr hp₀mem)
      intro x hx
      have hxA : algebraMap A₀ A x ∈ IsLocalRing.maximalIdeal A := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
        intro hu
        apply hx
        have h1 : IsUnit (e.symm (e x)) := by rw [heap]; exact hu.map e.symm
        rwa [RingEquiv.symm_apply_apply] at h1
      rw [hϖ, ← hp₀, Ideal.mem_span_singleton] at hxA
      obtain ⟨c, hc⟩ := hxA
      obtain ⟨c₀, rfl⟩ := hsurj c
      rw [← map_mul] at hc
      rw [Ideal.mem_span_singleton]
      exact ⟨c₀, hinj hc⟩
    have hassoc : Associated p₀ (q : A₀) := by
      rw [← Ideal.span_singleton_eq_span_singleton, ← hmax₀, hA₀q]
    obtain ⟨u, hu⟩ := hassoc
    have hp₀' : p₀ = (q : A₀) * ↑u⁻¹ := (Units.eq_mul_inv_iff_mul_eq u).mpr hu

    let σ : A →+* W₀ := (algebraMap A₀ W₀).comp e.symm.toRingHom
    have hσA₀ : ∀ a₀ : A₀, σ (algebraMap A₀ A a₀) = algebraMap A₀ W₀ a₀ := by
      intro a₀
      show algebraMap A₀ W₀ (e.symm (algebraMap A₀ A a₀)) = _
      rw [← heap, RingEquiv.symm_apply_apply]
    have hσϖ : σ ϖ = (q : W₀) * algebraMap A₀ W₀ (↑u⁻¹ : A₀) := by
      rw [← hp₀, hσA₀, hp₀', map_mul, map_natCast]
    have hunit : IsUnit (algebraMap A₀ W₀ (↑u⁻¹ : A₀)) := (Units.isUnit u⁻¹).map _
    refine ⟨W₀, inferInstance, inferInstance, inferInstance, inferInstance, RingHom.id W₀, σ, algebraMap W₀ R₀,
      inferInstance, RingHom.comp_id _, ?_, ?_, ?_, ?_⟩
    ·
      refine RingHom.ext fun a => ?_
      obtain ⟨a₀, rfl⟩ := hsurj a
      rw [RingHom.comp_apply, hσA₀, hσ₀]
    · intro a₀
      rw [hσA₀, RingHom.id_apply]
    ·
      rw [hW₀, hσϖ, Ideal.span_singleton_mul_right_unit hunit]
    · refine ⟨algebraMap A₀ W₀ (↑u⁻¹ : A₀), hunit, ?_⟩
      have h1 : q - 1 = 1 := by omega
      rw [h1, pow_one, hσϖ, mul_comm]

end S_IsPrimitiveRoot_exists_isDiscreteValuationRing_isAdicComplete_ringHom_comp_eq_maximalIdeal_eq_span_pow_sub_one_eq_mul_of_adjoin_eq_top_of_prime
end P2MW
export P2MW.S_IsPrimitiveRoot_exists_isDiscreteValuationRing_isAdicComplete_ringHom_comp_eq_maximalIdeal_eq_span_pow_sub_one_eq_mul_of_adjoin_eq_top_of_prime (solution)
