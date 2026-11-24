-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.sum_divisors_prime_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:51:37.534351+00:00
-- url     : https://prove2.me/submissions/839476a7-b0b6-4be5-877d-edee5ba877b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution {R : Type*} [CommRing R] (χ : ℕ → R)
    (hχ : ∀ a b, χ (a * b) = χ a * χ b) {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) :
    ∑ e ∈ (p * m).divisors, χ e = (1 + χ p) * ∑ e ∈ m.divisors, χ e
      - χ p * if p ∣ m then ∑ e ∈ (m / p).divisors, χ e else 0 := by
  have key : ∀ k, k ≠ 0 → ∑ e ∈ (p * k).divisors with p ∣ e, χ e
      = χ p * ∑ e ∈ k.divisors, χ e := by
    intro k hk
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun e _ => p * e) ?_ ?_ ?_ fun e _ => (hχ _ _).symm
    · intro e he
      simp only [Nat.mem_divisors, Finset.mem_filter] at he ⊢
      exact ⟨⟨Nat.mul_dvd_mul_left _ he.1, mul_ne_zero hp.ne_zero hk⟩, dvd_mul_right _ _⟩
    · intro e _ e' _ h
      exact Nat.eq_of_mul_eq_mul_left hp.pos h
    · intro e he
      simp only [Nat.mem_divisors, Finset.mem_filter] at he
      obtain ⟨⟨h1, -⟩, e, rfl⟩ := he
      exact ⟨e, Nat.mem_divisors.2 ⟨(Nat.mul_dvd_mul_iff_left hp.pos).1 h1, hk⟩, rfl⟩
  have e1 : ((p * m).divisors.filter fun e => ¬ p ∣ e) = m.divisors.filter fun e => ¬ p ∣ e := by
    ext e
    simp only [Nat.mem_divisors, Finset.mem_filter]
    refine ⟨fun h => ⟨⟨?_, hm⟩, h.2⟩, fun h => ⟨⟨h.1.1.mul_left _, mul_ne_zero hp.ne_zero hm⟩, h.2⟩⟩
    exact ((hp.coprime_iff_not_dvd.2 h.2).symm.dvd_mul_left).1 h.1.1
  have e2 : ∑ e ∈ m.divisors with p ∣ e, χ e
      = χ p * if p ∣ m then ∑ e ∈ (m / p).divisors, χ e else 0 := by
    split_ifs with h
    · obtain ⟨k, rfl⟩ := h
      rw [key k (right_ne_zero_of_mul hm), Nat.mul_div_cancel_left _ hp.pos]
    · rw [mul_zero]
      refine Finset.sum_eq_zero fun e he => ?_
      simp only [Nat.mem_divisors, Finset.mem_filter] at he
      exact absurd (he.2.trans he.1.1) h
  have e3 := Finset.sum_filter_add_sum_filter_not m.divisors (fun e => p ∣ e) χ
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun e => p ∣ e), key m hm, e1, ← e2]
  linear_combination e3
end GlobalTheory.QuadraticZeta
