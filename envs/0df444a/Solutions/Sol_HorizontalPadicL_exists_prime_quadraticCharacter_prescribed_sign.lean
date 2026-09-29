-- Prove2me | solution 1 for HorizontalPadicL.exists_prime_quadraticCharacter_prescribed_sign
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-26T20:18:22.352828+00:00
-- url     : https://prove2.me/submissions/ca231bce-0fec-4e94-9768-e94fc3359662

import Definitions.Def_KN_HorizontalPadicL
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Factorization.Induction

set_option autoImplicit false

namespace HorizontalPadicL

/-- The Legendre character of a prime modulus, with values in the algebraic numbers. -/
noncomputable def primeQuadraticCharacter (q : ℕ) [Fact q.Prime] :
    DirichletCharacter MTT.Qbar q :=
  (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom MTT.Qbar)

variable {q : ℕ} [Fact q.Prime]

@[simp]
lemma primeQuadraticCharacter_apply (a : ZMod q) :
    primeQuadraticCharacter q a = (quadraticChar (ZMod q) a : MTT.Qbar) := rfl

lemma primeQuadraticCharacter_isQuadratic : (primeQuadraticCharacter q).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod q)).comp (Int.castRingHom MTT.Qbar)

lemma primeQuadraticCharacter_ne_one (hq : q ≠ 2) : primeQuadraticCharacter q ≠ 1 := by
  apply (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom MTT.Qbar)
    Int.cast_injective).mpr
  exact quadraticChar_ne_one ((ZMod.ringChar_zmod_n q).trans_ne hq)

lemma orderOf_primeQuadraticCharacter (hq : q ≠ 2) :
    orderOf (primeQuadraticCharacter q) = 2 :=
  orderOf_eq_prime primeQuadraticCharacter_isQuadratic.sq_eq_one
    (primeQuadraticCharacter_ne_one hq)

lemma primeQuadraticCharacter_isPrimitive (hq : q ≠ 2) :
    (primeQuadraticCharacter q).IsPrimitive := by
  rcases (Nat.dvd_prime (Fact.out : q.Prime)).mp
    (primeQuadraticCharacter q).conductor_dvd_level with h | h
  · exact False.elim (primeQuadraticCharacter_ne_one hq
      (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
  · exact h

lemma primeQuadraticCharacter_neg_one (hq : q ≠ 2) :
    primeQuadraticCharacter q (-1) = (ZMod.χ₄ q : MTT.Qbar) := by
  change (quadraticChar (ZMod q) (-1) : MTT.Qbar) = _
  rw [quadraticChar_neg_one ((ZMod.ringChar_zmod_n q).trans_ne hq), ZMod.card]

lemma primeQuadraticCharacter_neg_one_of_mod_four_eq_one (hq : q % 4 = 1) :
    primeQuadraticCharacter q (-1) = 1 := by
  rw [primeQuadraticCharacter_neg_one (by omega), ZMod.χ₄_nat_one_mod_four hq]
  simp

lemma primeQuadraticCharacter_neg_one_of_mod_four_eq_three (hq : q % 4 = 3) :
    primeQuadraticCharacter q (-1) = -1 := by
  rw [primeQuadraticCharacter_neg_one (by omega), ZMod.χ₄_nat_three_mod_four hq]
  simp

/-- Either of the residue classes `1` and `-1` modulo `8 * A` contains arbitrarily
large primes. -/
theorem exists_prime_gt_congruent_sign (A : ℕ) (hA : 0 < A) (s : Bool) (b : ℕ) :
    ∃ q > b, q.Prime ∧ (q : ZMod (8 * A)) = if s then 1 else -1 := by
  have : NeZero (8 * A) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hA)⟩
  apply Nat.forall_exists_prime_gt_and_eq_mod (a := if s then 1 else -1) _ b
  cases s
  · exact isUnit_neg_one
  · exact isUnit_one

lemma primeQuadraticCharacter_neg_one_of_congruent_sign {A : ℕ} (s : Bool)
    (hq : (q : ZMod (8 * A)) = if s then 1 else -1) :
    primeQuadraticCharacter q (-1) = if s then 1 else -1 := by
  have hq4 : (q : ZMod 4) = if s then 1 else -1 := by
    have h := congrArg
      (ZMod.castHom (dvd_mul_of_dvd_left (by decide : 4 ∣ 8) A) (ZMod 4)) hq
    cases s <;>
      simpa only [Bool.false_eq_true, if_false, if_true, map_natCast, map_neg, map_one] using h
  cases s
  · apply primeQuadraticCharacter_neg_one_of_mod_four_eq_three
    have h := congrArg ZMod.val hq4
    simpa using h
  · apply primeQuadraticCharacter_neg_one_of_mod_four_eq_one
    have h := congrArg ZMod.val hq4
    norm_num at h ⊢
    exact h

lemma coprime_of_congruent_sign {A q : ℕ} (s : Bool)
    (hq : (q : ZMod (8 * A)) = if s then 1 else -1) : Nat.Coprime A q := by
  have hu : IsUnit (q : ZMod (8 * A)) := by
    rw [hq]
    cases s
    · exact isUnit_neg_one
    · exact isUnit_one
  exact ((ZMod.isUnit_iff_coprime q (8 * A)).mp hu).symm.of_dvd_left
    (dvd_mul_of_dvd_right (dvd_refl A) 8)

/-- There is a primitive quadratic character of prime conductor coprime to a given
positive integer, with either prescribed parity and a compatible prime congruence. -/
theorem exists_primitive_quadraticCharacter_congruent_sign
    (A : ℕ) (hA : 0 < A) (s : Bool) :
    ∃ η : DirichletCharacterWithLevel,
      η.1.1.Prime ∧
      (η.1.1 : ZMod (8 * A)) = (if s then 1 else -1) ∧
      η.2.IsPrimitive ∧ orderOf η.2 = 2 ∧ Nat.Coprime A η.2.conductor ∧
      η.2 (-1) = if s then 1 else -1 := by
  obtain ⟨q, hq2, hq, hcong⟩ := exists_prime_gt_congruent_sign A hA s 2
  have : Fact q.Prime := ⟨hq⟩
  have hp := primeQuadraticCharacter_isPrimitive (ne_of_gt hq2)
  refine ⟨⟨⟨q, hq.pos⟩, primeQuadraticCharacter q⟩, hq, hcong, hp,
    orderOf_primeQuadraticCharacter (ne_of_gt hq2), ?_,
    primeQuadraticCharacter_neg_one_of_congruent_sign s hcong⟩
  change Nat.Coprime A (primeQuadraticCharacter q).conductor
  rw [hp]
  exact coprime_of_congruent_sign s hcong

end HorizontalPadicL

namespace HorizontalPadicL

/-- The value of a multiplicative character at a positive integer is determined by
its values on the prime divisors. -/
lemma quadraticChar_nat_eq_one_of_prime_dvd {q N : ℕ} [Fact q.Prime]
    (hN : 0 < N)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ N → quadraticChar (ZMod q) (p : ZMod q) = 1) :
    quadraticChar (ZMod q) (N : ZMod q) = 1 := by
  have main : ∀ n : ℕ, n ≠ 0 → n ∣ N → quadraticChar (ZMod q) (n : ZMod q) = 1 := by
    apply Nat.recOnMul
    · simp
    · simp
    · intro p hp _ hpN
      exact hprime p hp hpN
    · intro a b ha hb hab0 habN
      rw [Nat.cast_mul, map_mul, ha (left_ne_zero_of_mul hab0)
        (dvd_trans (dvd_mul_right a b) habN), hb (right_ne_zero_of_mul hab0)
        (dvd_trans (dvd_mul_left b a) habN), one_mul]
  exact main N (Nat.ne_of_gt hN) dvd_rfl

/-- A prime congruent to either sign modulo `8 * A` sees every positive divisor
of `A` as a quadratic residue. -/
lemma quadraticChar_nat_eq_one_of_congruent_sign {A N q : ℕ} [Fact q.Prime]
    (hN : 0 < N) (hNA : N ∣ A) (s : Bool)
    (hq : (q : ZMod (8 * A)) = if s then 1 else -1) :
    quadraticChar (ZMod q) (N : ZMod q) = 1 := by
  have hcast (m : ℕ) (hm : m ∣ 8 * A) :
      (q : ZMod m) = if s then 1 else -1 := by
    have h := congrArg (ZMod.castHom hm (ZMod m)) hq
    simpa only [map_natCast, apply_ite, map_one, map_neg] using h
  have hq2 : q ≠ 2 := by
    have h2 := hcast 2 (dvd_mul_of_dvd_left (by decide : 2 ∣ 8) A)
    intro heq
    subst q
    rw [ZMod.natCast_self] at h2
    cases s <;> simp at h2
  have hchar : ringChar (ZMod q) ≠ 2 := by
    simpa only [ZMod.ringChar_zmod_n] using hq2
  have h4 : ZMod.χ₄ (q : ZMod 4) = if s then 1 else -1 := by
    rw [hcast 4 (dvd_mul_of_dvd_left (by decide : 4 ∣ 8) A)]
    cases s <;> decide
  have h8 : ZMod.χ₈ (q : ZMod 8) = 1 := by
    rw [hcast 8 (dvd_mul_right 8 A)]
    cases s <;> decide
  apply quadraticChar_nat_eq_one_of_prime_dvd hN
  intro p hp hpN
  have : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst p
    simpa only [Nat.cast_ofNat, quadraticChar_two hchar, ZMod.card] using h8
  have hqp : (q : ZMod p) = if s then 1 else -1 :=
    hcast p (dvd_mul_of_dvd_right (dvd_trans hpN hNA) 8)
  have hqp_ne : q ≠ p := by
    intro heq
    subst q
    cases s <;> simp at hqp
  rw [quadraticChar_odd_prime hchar hp2
    (by simpa only [ZMod.ringChar_zmod_n] using hqp_ne), ZMod.card, h4, hqp]
  cases s <;> simp

end HorizontalPadicL

open HorizontalPadicL

theorem solution
    (A : ℕ) (hA : 0 < A) (s : Bool) (b : ℕ) :
    ∃ η : DirichletCharacterWithLevel,
      η.1.1.Prime ∧ b < η.1.1 ∧
      (η.1.1 : ZMod (8 * A)) = (if s then 1 else -1) ∧
      η.2.IsPrimitive ∧ orderOf η.2 = 2 ∧ Nat.Coprime A η.2.conductor ∧
      η.2 (-1) = (if s then 1 else -1) ∧
      (∀ n : ℕ, 0 < n → n ∣ A → η.2 n = 1) := by
  obtain ⟨q, hbound, hq, hcong⟩ := exists_prime_gt_congruent_sign A hA s (max b 2)
  have : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := ne_of_gt (lt_of_le_of_lt (le_max_right b 2) hbound)
  have hprim := primeQuadraticCharacter_isPrimitive hq2
  refine ⟨⟨⟨q, hq.pos⟩, primeQuadraticCharacter q⟩, hq,
    lt_of_le_of_lt (le_max_left b 2) hbound, hcong, hprim,
    orderOf_primeQuadraticCharacter hq2, ?_,
    primeQuadraticCharacter_neg_one_of_congruent_sign s hcong, ?_⟩
  · change Nat.Coprime A (primeQuadraticCharacter q).conductor
    rw [hprim]
    exact coprime_of_congruent_sign s hcong
  · intro n hn hnA
    change primeQuadraticCharacter q (n : ZMod q) = 1
    rw [primeQuadraticCharacter_apply,
      quadraticChar_nat_eq_one_of_congruent_sign hn hnA s hcong, Int.cast_one]
