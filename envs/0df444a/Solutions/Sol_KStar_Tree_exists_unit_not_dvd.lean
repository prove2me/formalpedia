-- Prove2me | solution 1 for KStar.Tree.exists_unit_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:38.965894+00:00
-- url     : https://prove2.me/submissions/312bf434-4d86-4629-8ab2-671c9f7a738a

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuInf
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuSumApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace KStar.Tree
variable (l : ℕ) [Fact l.Prime]
private theorem nsa_isUnit {c : ℤ_[l]} (hc : ¬ (l : ℤ_[l]) ∣ c) : IsUnit c := by
  by_contra hu
  have : c ∈ IsLocalRing.maximalIdeal ℤ_[l] := hu
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  exact hc this
private theorem nsa_nat (k : ℕ) (m : ℕ) (h : (l : ℤ_[l]) ^ k ∣ (m : ℤ_[l])) : l ^ k ∣ m := by
  have := (PadicInt.pow_p_dvd_int_iff (p := l) k (m : ℤ)).1 (by simpa using h)
  exact_mod_cast this
private theorem nsa_lte (s n : ℕ) (hs : s ≠ 0) (hn : Odd n) :
    ¬ (l : ℤ) ^ (s + n.factorization l + 1) ∣ (1 + (l : ℤ) ^ s) ^ n - 1 := by
  have hp : l.Prime := Fact.out
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hxy : (l : ℤ) ∣ (1 + (l : ℤ) ^ s) - 1 := by
    simpa using dvd_pow_self (l : ℤ) hs
  have hx : ¬ (l : ℤ) ∣ 1 + (l : ℤ) ^ s := by
    intro h
    exact hpz.not_dvd_one ((dvd_add_left (dvd_pow_self (l : ℤ) hs)).1 h)
  have hs' : emultiplicity (l : ℤ) ((1 + (l : ℤ) ^ s) - 1) = s := by
    rw [add_sub_cancel_left]
    exact emultiplicity_pow_self_of_prime hpz s
  have key : emultiplicity (l : ℤ) ((1 + (l : ℤ) ^ s) ^ n - 1 ^ n) =
      ((s + n.factorization l : ℕ) : ℕ∞) := by
    by_cases hl : l = 2
    · have hnd : ¬ l ∣ n := by
        subst hl
        exact hn.not_two_dvd_nat
      rw [emultiplicity_pow_sub_pow_of_prime hpz hxy hx (by exact_mod_cast hnd), hs',
        Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
    · rw [Int.emultiplicity_pow_sub_pow hp (hp.odd_of_ne_two hl) hxy hx n, hs',
        Nat.factorization_def n hp, Nat.cast_add, padicValNat_eq_emultiplicity hn0]
  rw [one_pow] at key
  intro h
  have := le_emultiplicity_of_pow_dvd h
  rw [key] at this
  have := Nat.cast_le.1 this
  omega
end KStar.Tree
end

set_option autoImplicit false
open KStar KStar.Tree
variable (l : ℕ) [Fact l.Prime]
namespace KStar.Tree
theorem _root_.solution (C n : ℕ) (hC : C ≠ 0) (h2 : 2 ∣ C) (hn : Odd n) :
    ∃ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ C.factorization l ∣ (u : ℤ_[l]) - 1 ∧
      ¬ (l : ℤ_[l]) ^ (C.factorization l + (if l ∣ C then n.factorization l else 0) + 1) ∣ (u : ℤ_[l]) ^ n - 1 := by
  have hp : l.Prime := Fact.out
  by_cases hlC : l ∣ C
  · rw [if_pos hlC]
    have hs : C.factorization l ≠ 0 := (hp.factorization_pos_of_dvd hC hlC).ne'
    generalize C.factorization l = s at hs ⊢
    have hU : IsUnit (1 + (l : ℤ_[l]) ^ s) := by
      apply nsa_isUnit
      intro h
      exact PadicInt.prime_p.not_dvd_one ((dvd_add_left (dvd_pow_self (l : ℤ_[l]) hs)).1 h)
    refine ⟨hU.unit, by simp, fun h => nsa_lte l s n hs hn ?_⟩
    rw [← PadicInt.pow_p_dvd_int_iff]
    simpa using h
  · rw [if_neg hlC, Nat.factorization_eq_zero_of_not_dvd hlC]
    refine ⟨-1, by simp, fun h => hlC ?_⟩
    have e : ((-1 : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 = -((2 : ℕ) : ℤ_[l]) := by
      simp only [Units.val_neg, Units.val_one, hn.neg_one_pow]
      push_cast
      ring
    rw [e, dvd_neg] at h
    have := nsa_nat l _ _ h
    simp only [add_zero, zero_add, pow_one] at this
    exact this.trans h2
end KStar.Tree
