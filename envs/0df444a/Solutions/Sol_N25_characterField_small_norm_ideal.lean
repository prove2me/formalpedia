-- Prove2me | solution 1 for N25.characterField_small_norm_ideal
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:48.123012+00:00
-- url     : https://prove2.me/submissions/07fbe83f-fdf3-442f-876f-f572428e5b3e

import Mathlib
import Theorems.Thm_N25_characterField_prime_norm_small
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic

set_option autoImplicit false

noncomputable section

open scoped NumberField nonZeroDivisors

namespace N25

private theorem small_norm_proper_ideal_lower_bound (I : Ideal (𝓞 characterField))
    (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) (hbound : I.absNorm ≤ 24) : 5 ≤ I.absNorm := by
  obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal I hItop
  letI : P.IsMaximal := hPmax
  have hP0 : P ≠ ⊥ := fun h => hI0 (le_bot_iff.mp (h ▸ hIP))
  have hIpos : 0 < I.absNorm := Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hI0)
  have hle : P.absNorm ≤ I.absNorm :=
    Nat.le_of_dvd hIpos (Ideal.absNorm_dvd_absNorm_of_le hIP)
  have hsmall := characterField_prime_norm_small P hP0 (hle.trans hbound)
  omega

/-- Every nonzero ideal with norm at most 24 is the unit ideal or has norm
5 or 7; composite proper ideals already have norm at least 25. -/
theorem _root_.solution (I : (Ideal (𝓞 characterField))⁰)
    (hbound : Ideal.absNorm (I : Ideal (𝓞 characterField)) ≤ 24) :
    (I : Ideal (𝓞 characterField)) = ⊤ ∨
    Ideal.absNorm (I : Ideal (𝓞 characterField)) = 5 ∨
    Ideal.absNorm (I : Ideal (𝓞 characterField)) = 7 := by
  let J : Ideal (𝓞 characterField) := I
  have hJ0 : J ≠ ⊥ := by
    exact nonZeroDivisors.ne_zero I.property
  by_cases hJtop : J = ⊤
  · exact Or.inl hJtop
  have hnotunit : ¬ IsUnit J := by simpa only [Ideal.isUnit_iff] using hJtop
  have hirred : Irreducible J := by
    refine ⟨hnotunit, ?_⟩
    intro A B hAB
    by_cases hA : IsUnit A
    · exact Or.inl hA
    by_cases hB : IsUnit B
    · exact Or.inr hB
    exfalso
    have hA0 : A ≠ ⊥ := by intro h; simp [h] at hAB; exact hJ0 hAB
    have hB0 : B ≠ ⊥ := by intro h; simp [h] at hAB; exact hJ0 hAB
    have hApos : 0 < A.absNorm := Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hA0)
    have hBpos : 0 < B.absNorm := Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hB0)
    have hprod : J.absNorm = A.absNorm * B.absNorm := by rw [hAB, map_mul]
    have hAle : A.absNorm ≤ 24 := by nlinarith
    have hBle : B.absNorm ≤ 24 := by nlinarith
    have hAlower := small_norm_proper_ideal_lower_bound A hA0
      (by simpa only [Ideal.isUnit_iff] using hA) hAle
    have hBlower := small_norm_proper_ideal_lower_bound B hB0
      (by simpa only [Ideal.isUnit_iff] using hB) hBle
    nlinarith
  haveI : J.IsPrime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirred)
  exact Or.inr (characterField_prime_norm_small J hJ0 hbound)

end N25
