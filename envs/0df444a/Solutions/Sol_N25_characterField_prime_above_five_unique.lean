-- Prove2me | solution 1 for N25.characterField_prime_above_five_unique
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:56.119514+00:00
-- url     : https://prove2.me/submissions/efd9e562-463b-461c-aceb-13c716f11202

import Definitions.Def_N25_CharacterField
import Mathlib.NumberTheory.NumberField.Norm
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

open scoped NumberField

namespace N25

/-- There is at most one prime ideal over 5 in the literal H25-fixed field. -/
theorem _root_.solution
    (P₁ P₂ : Ideal (𝓞 characterField)) [P₁.IsPrime] [P₂.IsPrime]
    (hP₁ : P₁ ≠ ⊥) (hP₂ : P₂ ≠ ⊥)
    (h5₁ : (5 : 𝓞 characterField) ∈ P₁)
    (h5₂ : (5 : 𝓞 characterField) ∈ P₂) : P₁ = P₂ := by
  let ζ : 𝓞 cyclotomicField :=
    ⟨IsCyclotomicExtension.zeta 25 ℚ cyclotomicField,
      (IsCyclotomicExtension.zeta_spec 25 ℚ cyclotomicField).isIntegral (by decide)⟩
  let T : Ideal (𝓞 cyclotomicField) := Ideal.span {ζ - 1}
  have hζ : IsPrimitiveRoot (ζ : cyclotomicField) (5 ^ (1 + 1)) :=
    IsCyclotomicExtension.zeta_spec 25 ℚ cyclotomicField
  have hnorm : Algebra.norm ℚ ((ζ : cyclotomicField) - 1) = 5 := by
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    haveI : IsCyclotomicExtension {5 ^ (1 + 1)} ℚ cyclotomicField := by
      change IsCyclotomicExtension {25} ℚ cyclotomicField
      infer_instance
    exact hζ.norm_sub_one_of_prime_ne_two
      (Polynomial.cyclotomic.irreducible_rat (by decide)) (by decide)
  have hnormZ : Algebra.norm ℤ (ζ - 1) = 5 := by
    have he := Algebra.coe_norm_int (ζ - 1)
    change (Algebra.norm ℤ (ζ - 1) : ℚ) =
      Algebra.norm ℚ ((ζ : cyclotomicField) - 1) at he
    rw [hnorm] at he
    exact_mod_cast he
  have hTnorm : T.absNorm = 5 := by
    change (Ideal.span {ζ - 1}).absNorm = 5
    rw [Ideal.absNorm_span_singleton, hnormZ]
    norm_num
  haveI : T.IsPrime := Ideal.isPrime_of_irreducible_absNorm
    (by rw [hTnorm]; exact Nat.prime_five)
  have hTzero : T ≠ ⊥ := by
    intro h
    simpa [h] using hTnorm
  haveI : T.IsMaximal := (inferInstance : T.IsPrime).isMaximal hTzero
  have hunique (Q : Ideal (𝓞 cyclotomicField)) [Q.IsPrime]
      (h5 : (5 : 𝓞 cyclotomicField) ∈ Q) : Q = T := by
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    haveI : CharP ((𝓞 cyclotomicField) ⧸ Q) 5 :=
      (CharP.charP_iff_prime_eq_zero Nat.prime_five).mpr
        (by simpa only [Nat.cast_ofNat, map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr h5)
    have hbar : (Ideal.Quotient.mk Q ζ) ^ 25 = 1 := by
      rw [← map_pow]
      have hp : ζ ^ 25 = 1 := by
        apply Subtype.ext
        exact hζ.pow_eq_one
      rw [hp, map_one]
    have hzero : Ideal.Quotient.mk Q (ζ - 1) = 0 := by
      apply eq_zero_of_pow_eq_zero (n := 25)
      rw [map_sub, map_one]
      change (Ideal.Quotient.mk Q ζ - 1) ^ (5 ^ 2) = 0
      rw [sub_pow_char_pow]
      change (Ideal.Quotient.mk Q ζ) ^ 25 - 1 ^ 25 = 0
      rw [hbar, one_pow, sub_self]
    have hle : T ≤ Q := Ideal.span_le.mpr (by
      intro x hx
      have hx' : x = ζ - 1 := Set.mem_singleton_iff.mp hx
      rw [hx']
      exact Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    exact ((inferInstance : T.IsMaximal).eq_of_le (inferInstance : Q.IsPrime).ne_top hle).symm
  haveI : P₁.IsMaximal := (inferInstance : P₁.IsPrime).isMaximal hP₁
  haveI : P₂.IsMaximal := (inferInstance : P₂.IsPrime).isMaximal hP₂
  obtain ⟨Q₁, hQ₁, hQ₁P₁⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 cyclotomicField) P₁ (by simp)
  obtain ⟨Q₂, hQ₂, hQ₂P₂⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 cyclotomicField) P₂ (by simp)
  letI : Q₁.IsMaximal := hQ₁
  letI : Q₂.IsMaximal := hQ₂
  have h5Q₁ : (5 : 𝓞 cyclotomicField) ∈ Q₁ := by
    have hh : (5 : 𝓞 characterField) ∈ Q₁.comap (algebraMap _ _) := hQ₁P₁.symm ▸ h5₁
    simpa only [Ideal.mem_comap, map_ofNat] using hh
  have h5Q₂ : (5 : 𝓞 cyclotomicField) ∈ Q₂ := by
    have hh : (5 : 𝓞 characterField) ∈ Q₂.comap (algebraMap _ _) := hQ₂P₂.symm ▸ h5₂
    simpa only [Ideal.mem_comap, map_ofNat] using hh
  have hQeq : Q₁ = Q₂ := (hunique Q₁ h5Q₁).trans (hunique Q₂ h5Q₂).symm
  exact hQ₁P₁.symm.trans ((congrArg (Ideal.comap (algebraMap (𝓞 characterField)
    (𝓞 cyclotomicField))) hQeq).trans hQ₂P₂)

end N25
