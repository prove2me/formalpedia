-- Prove2me | solution 1 for MersenneLPW.infinitude_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:34:02.785207+00:00
-- url     : https://prove2.me/submissions/50883dc0-0cf5-442d-93d0-8cefb31c3b68

import Mathlib

namespace EEAux

open ArithmeticFunction Finset

-- access notation `σ`
open scoped sigma

theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- Euclid's theorem that Mersenne primes induce perfect numbers -/
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ', ← sigma_one_apply,
    mul_comm,
    isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right (by simp)).pow_right _),
    sigma_two_pow_eq_mersenne_succ]
  · simp [pr, sigma_one_apply]
  · positivity

theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro H
  simp [H, mersenne, Nat.not_prime_one] at pr

theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by simp [ne_zero_of_prime_mersenne k pr, parity_simps]

theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-- **Perfect Number Theorem**: Euler's theorem that even perfect numbers can be factored as a
  power of two times a Mersenne prime. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose hm
    simp [hm]


theorem even_and_perfect_iff {n : ℕ} :
    Even n ∧ Nat.Perfect n ↔ ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧
      n = 2 ^ k * mersenne (k + 1) := by
  constructor
  · rintro ⟨ev, perf⟩
    exact eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf
  · rintro ⟨k, pr, rfl⟩
    exact ⟨even_two_pow_mul_mersenne_of_prime k pr, perfect_two_pow_mul_mersenne_of_prime k pr⟩

end EEAux

theorem solution :
    {p : ℕ | (mersenne p).Prime}.Infinite ↔ {n : ℕ | Even n ∧ Nat.Perfect n}.Infinite := by
  -- the even perfect numbers are the image of {k | M(k+1) prime} under k ↦ 2^k M(k+1)
  have hset : {n : ℕ | Even n ∧ Nat.Perfect n} =
      (fun k : ℕ => 2 ^ k * mersenne (k + 1)) '' {k : ℕ | (mersenne (k + 1)).Prime} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_image, EEAux.even_and_perfect_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  have hinj : Function.Injective (fun k : ℕ => 2 ^ k * mersenne (k + 1)) := by
    apply StrictMono.injective
    apply strictMono_nat_of_lt_succ
    intro k
    have h1 : mersenne (k + 1) < mersenne (k + 1 + 1) := mersenne_lt_mersenne.2 (by omega)
    have h2 : 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 0 < 2 ^ k := by positivity
    calc 2 ^ k * mersenne (k + 1) < 2 ^ k * mersenne (k + 1 + 1) :=
          Nat.mul_lt_mul_of_pos_left h1 h3
      _ ≤ 2 ^ (k + 1) * mersenne (k + 1 + 1) := Nat.mul_le_mul_right _ h2
  have hshift : {p : ℕ | (mersenne p).Prime} = (fun k => k + 1) '' {k : ℕ | (mersenne (k + 1)).Prime} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hp
      rcases p with _ | k
      · exact absurd hp (by simp [mersenne, Nat.not_prime_zero])
      · exact ⟨k, hp, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact hk
  rw [hset, hshift, Set.infinite_image_iff hinj.injOn,
    Set.infinite_image_iff (fun a _ b _ h => by simpa using h)]
