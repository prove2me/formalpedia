-- Prove2me | solution 1 for HorizontalPadicL.realizedHorizontalCharacter_even_of_odd_prime_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:30:04.997793+00:00
-- url     : https://prove2.me/submissions/ac31509f-85d4-4dd3-b3dc-267dc582c0e2

import Definitions.Def_KN_SeededInverseThetaSystemV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Every element of the finite horizontal group is killed by `p ^ (A.sup m)`. -/
theorem horizontalFiniteGroup_pow_eq_one (p : ℕ) (m : ℕ → ℕ) (A : Finset ℕ)
    (g : HorizontalFiniteGroup p m A) : g ^ (p ^ A.sup m) = 1 := by
  funext i
  have hle : m i.1 ≤ A.sup m := Finset.le_sup (f := m) i.2
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
  show (g i) ^ (p ^ A.sup m) = 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, hc, pow_add, mul_comm, mul_nsmul, nsmul_eq_mul]
  simp

theorem realizedHorizontalCharacter_even_of_odd_prime
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (hR : R.HasExpectedProperties) (hpodd : p ≠ 2)
    (χ : HorizontalCharacter p L.exponent) :
    (R.realized χ).2 (-1) = 1 := by
  set M := p ^ χ.support.sup L.exponent with hM
  have hχ : χ.toMonoidHom ^ M = 1 := by
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, ← map_pow, horizontalFiniteGroup_pow_eq_one, map_one,
      MonoidHom.one_apply]
  have hψ : (R.realized χ).2 ^ M = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hR.1 χ, orderOf_dvd_iff_pow_eq_one]
    exact hχ
  have hpos : M ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  set x := (R.realized χ).2 (-1) with hx
  have h1 : x ^ M = 1 := by
    rw [hx, ← MulChar.pow_apply' _ hpos, hψ, MulChar.one_apply (isUnit_one.neg)]
  have h2 : x ^ 2 = 1 := by
    rw [hx, ← map_pow, neg_one_sq, map_one]
  have hcop : Nat.Coprime M 2 := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes (Fact.out) Nat.prime_two).2 hpodd
  have := (pow_gcd_eq_one (a := x) (m := M) (n := 2)).2 ⟨h1, h2⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

end HorizontalPadicL


-- Platform entry point: restates the target verbatim.
namespace HorizontalPadicL

/-- A realized horizontal character is even when the horizontal prime is odd:
its order is a power of `p`, while its value at `-1` has order at most two. -/
theorem _root_.solution
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (hR : R.HasExpectedProperties) (hpodd : p ≠ 2)
    (χ : HorizontalCharacter p L.exponent) :
    (R.realized χ).2 (-1) = 1 := by
  apply @HorizontalPadicL.realizedHorizontalCharacter_even_of_odd_prime <;> assumption

end HorizontalPadicL
