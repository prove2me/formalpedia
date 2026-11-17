-- Prove2me | solution 1 for N25.characterField_primes_over_seven_count
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:47.51452+00:00
-- url     : https://prove2.me/submissions/09e05ea8-dd27-49ba-b7b9-624385339762

import Mathlib
import Theorems.Thm_N25_characterField_degree_and_totallyReal
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25
import Mathlib.NumberTheory.RamificationInertia.Galois

set_option autoImplicit false

noncomputable section

open scoped NumberField

namespace N25

/-- At most five primes of the literal quintic field lie over 7. -/
theorem _root_.solution :
    (Ideal.primesOver (Ideal.span {(7 : ℤ)}) (𝓞 characterField)).ncard ≤ 5 := by
  haveI : IsGalois ℚ cyclotomicField :=
    IsCyclotomicExtension.isGalois {25} ℚ cyclotomicField
  haveI : characterSubgroup.Normal := ⟨by
    intro n hn g
    change cyclotomicAutEquiv (g * n * g⁻¹) ∈ H25
    have heq : cyclotomicAutEquiv (g * n * g⁻¹) = cyclotomicAutEquiv n := by
      simp only [map_mul, map_inv]
      simp [mul_comm, mul_assoc]
    rw [heq]
    exact hn⟩
  haveI : IsGalois ℚ characterField :=
    IsGalois.of_fixedField_normal_subgroup characterSubgroup
  let p : Ideal ℤ := Ideal.span {(7 : ℤ)}
  have hp0 : p ≠ ⊥ := by simp [p, Ideal.span_singleton_eq_bot]
  haveI : p.IsPrime := (Ideal.span_singleton_prime (by norm_num : (7 : ℤ) ≠ 0)).mpr (by norm_num)
  haveI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp0
  have he := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p
    (𝓞 characterField) (characterField ≃ₐ[ℚ] characterField)
  rw [IsGaloisGroup.card_eq_finrank (characterField ≃ₐ[ℚ] characterField) ℚ characterField,
    characterField_degree_and_totallyReal.1] at he
  have hw : 1 ≤ p.ramificationIdxIn (𝓞 characterField) * p.inertiaDegIn (𝓞 characterField) := by
    apply Nat.one_le_iff_ne_zero.mpr
    exact mul_ne_zero (Ideal.ramificationIdxIn_ne_zero (B := 𝓞 characterField)
      (G := characterField ≃ₐ[ℚ] characterField))
      (Ideal.inertiaDegIn_ne_zero (B := 𝓞 characterField)
        (G := characterField ≃ₐ[ℚ] characterField))
  have hle := Nat.mul_le_mul_left (Ideal.primesOver p (𝓞 characterField)).ncard hw
  simpa only [mul_one, he] using hle

end N25
