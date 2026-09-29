-- Prove2me | solution 1 for MTT.Eigenform.friedberg_hoffstein_nonzero_of_hasMinimalLevel
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-26T20:02:32.011822+00:00
-- url     : https://prove2.me/submissions/0e2c9e53-d960-4b81-96b5-3e42af47124b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_KN_HorizontalPadicL
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_MTT_Arithmetic
import Theorems.Thm_MTT_Eigenform_exists_frickeRootNumber_quadratic_twist
import Theorems.Thm_MTT_Eigenform_friedberg_hoffstein_infinite_of_admissible_seed

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

namespace MTT.Eigenform

/-- A normalized eigenform is nonzero as a function. -/
theorem exists_form_ne_zero {N k : ℕ} {ι : Qbar →+* ℂ} (f : Eigenform N k ι) :
    ∃ z : UpperHalfPlane, f.form z ≠ 0 := by
  by_contra! h
  have hf : (f.form : UpperHalfPlane → ℂ) = 0 := funext h
  have hcoeff := f.coeff_eq 1
  simp [hf, UpperHalfPlane.qExpansion_zero, f.normalized] at hcoeff

/-- The nebentype of a normalized eigenform of even weight is even. -/
theorem epsilon_neg_one_eq_one {N k : ℕ} {ι : Qbar →+* ℂ}
    (f : Eigenform N k ι) (heven : Even k) : f.epsilon (-1) = 1 := by
  obtain ⟨z, hz⟩ := f.exists_form_ne_zero
  let γ : CongruenceSubgroup.Gamma0 N := ⟨-1, by simp⟩
  have h := f.character_law γ z
  have hact : Matrix.SpecialLinearGroup.mapGL ℝ γ.val • z = z := by
    change (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z = z
    simp
  rw [hact] at h
  have h' : f.form z = ι (f.epsilon (-1)) * f.form z := by
    simpa [γ, heven.neg_one_pow] using h
  apply ι.injective
  rw [map_one]
  exact (mul_right_cancel₀ hz (by simpa using h'.symm) : ι (f.epsilon (-1)) = 1)

end MTT.Eigenform

namespace HorizontalPadicL

/-- For an even nebentype, a quadratic character of either parity can be chosen
with conductor avoiding `N * d` and with the two other root-number factors fixed. -/
theorem exists_quadratic_seed_of_sign {N : ℕ} (hN : 0 < N)
    (ε : DirichletCharacter MTT.Qbar N) (hε : ε (-1) = 1)
    (d : ℕ) (hd : 0 < d) (s : Bool) :
    ∃ η : DirichletCharacterWithLevel,
      η.2.IsPrimitive ∧ orderOf η.2 = 2 ∧ Nat.Coprime (N * d) η.1.1 ∧
      ε η.1.1 = 1 ∧ η.2 (-N) = (if s then 1 else -1) := by
  obtain ⟨q, hq2, hq, hcong⟩ :=
    exists_prime_gt_congruent_sign (N * d) (Nat.mul_pos hN hd) s 2
  have : Fact q.Prime := ⟨hq⟩
  have hqN : (q : ZMod N) = if s then 1 else -1 := by
    have h := congrArg
      (ZMod.castHom (dvd_mul_of_dvd_right (dvd_mul_right N d) 8) (ZMod N)) hcong
    simpa only [map_natCast, apply_ite, map_one, map_neg] using h
  have hεq : ε q = 1 := by
    rw [hqN]
    cases s <;> simp [hε]
  have hχN : primeQuadraticCharacter q (N : ZMod q) = 1 := by
    rw [primeQuadraticCharacter_apply,
      quadraticChar_nat_eq_one_of_congruent_sign hN (dvd_mul_right N d) s hcong]
    simp
  refine ⟨⟨⟨q, hq.pos⟩, primeQuadraticCharacter q⟩,
    primeQuadraticCharacter_isPrimitive (ne_of_gt hq2),
    orderOf_primeQuadraticCharacter (ne_of_gt hq2),
    coprime_of_congruent_sign s hcong, hεq, ?_⟩
  change primeQuadraticCharacter q (-(N : ZMod q)) = _
  rw [neg_eq_neg_one_mul, map_mul, hχN, mul_one]
  exact primeQuadraticCharacter_neg_one_of_congruent_sign s hcong

end HorizontalPadicL

open HorizontalPadicL

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (hmin : f.HasMinimalLevel) (d : ℕ) (hd : 0 < d) :
    ∃ η : DirichletCharacterWithLevel,
      η.2.IsPrimitive ∧
      orderOf η.2 = 2 ∧
      Nat.Coprime (N * d) η.2.conductor ∧
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0 := by
  classical
  obtain ⟨w, _, _, hsign, htwist⟩ :=
    f.exists_frickeRootNumber_quadratic_twist hN hk heven ι hmin
  obtain ⟨s, hs⟩ : ∃ s : Bool,
      f.HasRealCoefficients → w * (if s then (1 : ℂ) else -1) = 1 := by
    by_cases hreal : f.HasRealCoefficients
    · rcases hsign hreal with hw | hw
      · exact ⟨true, fun _ ↦ by simp [hw]⟩
      · exact ⟨false, fun _ ↦ by simp [hw]⟩
    · exact ⟨true, fun h ↦ (hreal h).elim⟩
  obtain ⟨η₀, hprimitive, horder, hcop, hε, hηN⟩ :=
    exists_quadratic_seed_of_sign hN f.epsilon (f.epsilon_neg_one_eq_one heven) d hd s
  have hadmissible : f.HasRealCoefficients →
      MTT.HasFrickeRootNumber
        (@MTT.inverseTwist ι f.form η₀.1.1 ⟨Nat.ne_of_gt η₀.1.2⟩ η₀.2)
        (N * η₀.1.1 ^ 2) k 1 := by
    intro hreal
    have hroot := htwist η₀ hprimitive horder (Nat.coprime_mul_iff_left.mp hcop).1
    have hscalar : w * ι (f.epsilon η₀.1.1) * ι (η₀.2 (-N)) = 1 := by
      rw [hε, map_one, mul_one, hηN]
      simpa only [apply_ite, map_one, map_neg] using hs hreal
    simpa only [hscalar] using hroot
  obtain ⟨η, hη⟩ :=
    (f.friedberg_hoffstein_infinite_of_admissible_seed hN hk heven ι hmin d hd
      η₀ hprimitive horder hcop hadmissible).nonempty
  exact ⟨η, hη.1, hη.2.1, hη.2.2.1, hη.2.2.2.2.2⟩
