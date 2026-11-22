-- Prove2me | solution 1 for NConjecture.abc_exponent_sharp
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T09:23:26.530633+00:00
-- url     : https://prove2.me/submissions/6b420fd8-ceb9-44db-abf0-cc56bd763581

import Mathlib
import Definitions.Def_Brocard_Defs
namespace NConjecture

theorem AuxSH_N (m : ℕ) : ∃ q, 3 ^ (2 ^ (m + 1)) = 2 ^ (m + 3) * q + 1 := by
  induction m with
  | zero => exact ⟨1, by norm_num⟩
  | succ m ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨2 ^ (m + 2) * q ^ 2 + q, ?_⟩
    rw [show 2 ^ (m + 1 + 1) = 2 ^ (m + 1) * 2 by ring, pow_mul, hq]
    ring

theorem AuxSH_rad_le (n : ℕ) (hn : n ≠ 0) : Brocard.radical n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

theorem AuxSH_union (s t : Finset ℕ) (hs : ∀ p ∈ s ∩ t, 0 < p) :
    ∏ p ∈ s ∪ t, p ≤ (∏ p ∈ s, p) * ∏ p ∈ t, p := by
  rw [← Finset.prod_union_inter]
  exact Nat.le_mul_of_pos_right _ (Finset.prod_pos hs)

theorem abc_exponent_sharp (ε : ℝ) (hε : 0 < ε) :
    Set.Infinite {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ Nat.Coprime t.1 t.2.1 ∧
      t.1 + t.2.1 = t.2.2 ∧
      (Brocard.radical (t.1 * t.2.1 * t.2.2) : ℝ) ^ (1 - ε) < (t.2.2 : ℝ)} := by
  let f : ℕ → ℕ × ℕ × ℕ := fun m => (1, 3 ^ (2 ^ (m + 1)) - 1, 3 ^ (2 ^ (m + 1)))
  have hinj : Function.Injective f := by
    intro m1 m2 h
    simp only [f, Prod.mk.injEq] at h
    have h1 := Nat.pow_right_injective (le_refl 2) (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h.2.2)
    omega
  refine Set.infinite_of_injective_forall_mem hinj (fun m => ?_)
  obtain ⟨q, hq⟩ := AuxSH_N m
  have hq0 : q ≠ 0 := by
    rintro rfl
    have : 3 ^ (2 ^ (m + 1)) = 1 := by simpa using hq
    have h2 : 1 < 3 ^ (2 ^ (m + 1)) := Nat.one_lt_pow (by positivity) (by norm_num)
    omega
  have hb : 3 ^ (2 ^ (m + 1)) - 1 = 2 ^ (m + 3) * q := by omega
  simp only [f, Set.mem_setOf_eq]
  rw [hb, hq]
  refine ⟨by norm_num, by positivity, Nat.coprime_one_left _, by ring, ?_⟩
  -- radical bound
  have hpfb : (2 ^ (m + 3) * q).primeFactors = (2 * q).primeFactors := by
    rw [Nat.primeFactors_mul (by positivity) hq0, Nat.primeFactors_mul (by norm_num) hq0,
      Nat.primeFactors_prime_pow (by omega) Nat.prime_two, Nat.prime_two.primeFactors]
  have hpfc : (2 ^ (m + 3) * q + 1).primeFactors = {3} := by
    rw [← hq, Nat.primeFactors_prime_pow (by positivity) Nat.prime_three]
  have hrad : Brocard.radical (1 * (2 ^ (m + 3) * q) * (2 ^ (m + 3) * q + 1)) ≤ 2 * q * 3 := by
    unfold Brocard.radical
    rw [one_mul, Nat.primeFactors_mul (by positivity) (by omega), hpfb, hpfc]
    refine (AuxSH_union _ _ (fun p hp => ?_)).trans ?_
    · exact (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hp).1).pos
    · rw [Finset.prod_singleton]
      exact Nat.mul_le_mul_right 3 (AuxSH_rad_le (2 * q) (by omega))
  have h8 : 8 ≤ 2 ^ (m + 3) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (m + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : Brocard.radical (1 * (2 ^ (m + 3) * q) * (2 ^ (m + 3) * q + 1)) < 2 ^ (m + 3) * q + 1 := by
    have : 2 * q * 3 < 2 ^ (m + 3) * q + 1 := by nlinarith
    omega
  have hr1 : 1 ≤ Brocard.radical (1 * (2 ^ (m + 3) * q) * (2 ^ (m + 3) * q + 1)) :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have hr1' : (1 : ℝ) ≤ (Brocard.radical (1 * (2 ^ (m + 3) * q) * (2 ^ (m + 3) * q + 1)) : ℝ) := by
    exact_mod_cast hr1
  calc (Brocard.radical (1 * (2 ^ (m + 3) * q) * (2 ^ (m + 3) * q + 1)) : ℝ) ^ (1 - ε)
      ≤ (Brocard.radical (1 * (2 ^ (m + 3) * q) * (2 ^ (m + 3) * q + 1)) : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hr1' (by linarith)
    _ = (Brocard.radical (1 * (2 ^ (m + 3) * q) * (2 ^ (m + 3) * q + 1)) : ℝ) := Real.rpow_one _
    _ < ((2 ^ (m + 3) * q + 1 : ℕ) : ℝ) := by exact_mod_cast hlt

end NConjecture

theorem solution (ε : ℝ) (hε : 0 < ε) :
    Set.Infinite {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ Nat.Coprime t.1 t.2.1 ∧
      t.1 + t.2.1 = t.2.2 ∧
      (Brocard.radical (t.1 * t.2.1 * t.2.2) : ℝ) ^ (1 - ε) < (t.2.2 : ℝ)} :=
  NConjecture.abc_exponent_sharp ε hε
