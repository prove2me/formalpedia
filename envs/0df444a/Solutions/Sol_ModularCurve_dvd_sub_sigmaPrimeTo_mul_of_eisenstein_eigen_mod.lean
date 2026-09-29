-- Prove2me | solution 1 for ModularCurve.dvd_sub_sigmaPrimeTo_mul_of_eisenstein_eigen_mod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/69c2d55f-a5f7-5f57-aa73-aa47bf3e3f90

import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Set
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_dvd_sub_sigmaPrimeTo_mul_of_eisenstein_eigen_mod

set_option autoImplicit false

open ModularCurve

namespace S09A1U

open Finset

variable {p : ℕ}

abbrev pdiv (p n : ℕ) : Finset ℕ := n.divisors.filter (fun d => ¬ p ∣ d)

theorem sigmaPrimeTo_eq (n : ℕ) : ModularCurve.sigmaPrimeTo p n = ∑ d ∈ pdiv p n, d := rfl

theorem sigmaPrimeTo_one (hp : p.Prime) : ModularCurve.sigmaPrimeTo p 1 = 1 := by
  rw [sigmaPrimeTo_eq]
  have : pdiv p 1 = {1} := by
    ext d
    simp only [pdiv, mem_filter, Nat.mem_divisors, Nat.dvd_one, ne_eq, one_ne_zero, not_false_eq_true, and_true,
      mem_singleton]
    constructor
    · rintro ⟨rfl, -⟩; rfl
    · rintro rfl; exact ⟨rfl, fun h => hp.one_lt.ne' (Nat.dvd_one.mp h)⟩
  rw [this, sum_singleton]

theorem sigmaPrimeTo_mul_self (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    ModularCurve.sigmaPrimeTo p (n * p) = ModularCurve.sigmaPrimeTo p n := by
  rw [sigmaPrimeTo_eq, sigmaPrimeTo_eq]
  congr 1
  ext d
  simp only [pdiv, mem_filter, Nat.mem_divisors, ne_eq, mul_eq_zero, hn, hp.ne_zero, or_self, not_false_eq_true,
    and_true]
  constructor
  · rintro ⟨hd, hpd⟩
    exact ⟨(Nat.Coprime.dvd_of_dvd_mul_right ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd))) hd), hpd⟩
  · rintro ⟨hd, hpd⟩
    exact ⟨Dvd.dvd.mul_right hd p, hpd⟩

theorem pdiv_mul (hp : p.Prime) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) {n : ℕ} (hn : n ≠ 0) :
    pdiv p (n * ℓ) = pdiv p n ∪ (pdiv p n).image (fun d => ℓ * d) := by
  ext d
  simp only [pdiv, mem_union, mem_image, mem_filter, Nat.mem_divisors, ne_eq, mul_eq_zero, hn, hℓ.ne_zero, or_self,
    not_false_eq_true, and_true]
  constructor
  · rintro ⟨hd, hpd⟩
    by_cases hℓd : ℓ ∣ d
    · obtain ⟨e, rfl⟩ := hℓd
      right
      refine ⟨e, ⟨?_, fun h => hpd (Dvd.dvd.mul_left h ℓ)⟩, rfl⟩
      rw [mul_comm n ℓ] at hd
      exact Nat.dvd_of_mul_dvd_mul_left hℓ.pos hd
    · left
      exact ⟨(Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓd)) hd), hpd⟩
  · rintro (⟨hd, hpd⟩ | ⟨e, ⟨he, hpe⟩, rfl⟩)
    · exact ⟨Dvd.dvd.mul_right hd ℓ, hpd⟩
    · refine ⟨by rw [mul_comm n ℓ]; exact Nat.mul_dvd_mul_left ℓ he, ?_⟩
      intro h
      exact hpe ((Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp hℓ).mpr (Ne.symm hℓp))) h)

theorem pdiv_inter_image (hp : p.Prime) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) {n : ℕ} (hn : n ≠ 0) :
    pdiv p n ∩ (pdiv p n).image (fun d => ℓ * d)
      = if ℓ ∣ n then (pdiv p (n / ℓ)).image (fun d => ℓ * d) else ∅ := by
  ext d
  split_ifs with hℓn
  · obtain ⟨n', rfl⟩ := hℓn
    have hn' : n' ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.mul_div_cancel_left n' hℓ.pos]
    simp only [pdiv, mem_inter, mem_image, mem_filter, Nat.mem_divisors, ne_eq, mul_eq_zero, hℓ.ne_zero, hn', or_self,
      not_false_eq_true, and_true]
    constructor
    · rintro ⟨⟨hd, hpd⟩, e, ⟨-, -⟩, rfl⟩
      exact ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left hℓ.pos hd, fun h => hpd (Dvd.dvd.mul_left h ℓ)⟩, rfl⟩
    · rintro ⟨e, ⟨he, hpe⟩, rfl⟩
      refine ⟨⟨Nat.mul_dvd_mul_left ℓ he, ?_⟩, e, ⟨Dvd.dvd.mul_left he ℓ, hpe⟩, rfl⟩
      intro h
      exact hpe (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp hℓ).mpr (Ne.symm hℓp)) h)
  · simp only [pdiv, mem_inter, mem_image, mem_filter, Nat.mem_divisors, ne_eq, hn, not_false_eq_true, and_true,
      notMem_empty, iff_false, not_and, not_exists]
    rintro ⟨hd, -⟩ e ⟨-, -⟩ rfl
    exact hℓn (dvd_trans (Dvd.intro e rfl) hd)

open Finset

variable {p : ℕ}

theorem sum_image_mul (ℓ : ℕ) (hℓ : ℓ ≠ 0) (s : Finset ℕ) : ∑ d ∈ s.image (fun d => ℓ * d), d = ℓ * ∑ d ∈ s, d := by
  rw [sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hℓ) h), mul_sum]

theorem sigmaPrimeTo_mul_prime (hp : p.Prime) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) {n : ℕ} (hn : n ≠ 0) :
    ModularCurve.sigmaPrimeTo p (n * ℓ) + (if ℓ ∣ n then ℓ * ModularCurve.sigmaPrimeTo p (n / ℓ) else 0)
      = (1 + ℓ) * ModularCurve.sigmaPrimeTo p n := by
  have h := sum_union_inter (s₁ := pdiv p n) (s₂ := (pdiv p n).image (fun d => ℓ * d)) (f := fun d => d)
  rw [← pdiv_mul hp hℓ hℓp hn, pdiv_inter_image hp hℓ hℓp hn, sum_image_mul ℓ hℓ.ne_zero] at h
  simp only [sigmaPrimeTo_eq]
  by_cases hℓn : ℓ ∣ n
  · rw [if_pos hℓn, sum_image_mul ℓ hℓ.ne_zero] at h
    rw [if_pos hℓn, h]; ring
  · rw [if_neg hℓn, sum_empty, add_zero] at h
    rw [if_neg hℓn, add_zero, h]; ring

theorem dvd_sub_sigmaPrimeTo_mul (hp : p.Prime) (m : ℕ) (af : ℕ → ℤ)
    (hT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ, n ≠ 0 →
      (m : ℤ) ∣ af (n * ℓ) + (if ℓ ∣ n then (ℓ : ℤ) * af (n / ℓ) else 0) - (1 + ℓ) * af n)
    (hU : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af (n * p) - af n) :
    ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (ModularCurve.sigmaPrimeTo p n : ℤ) * af 1 := by

  suffices H : ∀ n : ℕ, n ≠ 0 → ((af n : ℤ) : ZMod m) = (ModularCurve.sigmaPrimeTo p n : ZMod m) * (af 1 : ZMod m) by
    intro n hn
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [H n hn, sub_self]
  have hT' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ, n ≠ 0 →
      ((af (n * ℓ) : ℤ) : ZMod m) + (if ℓ ∣ n then (ℓ : ZMod m) * (af (n / ℓ) : ZMod m) else 0)
        = (1 + (ℓ : ZMod m)) * (af n : ZMod m) := by
    intro ℓ hℓ hℓp n hn
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr (hT ℓ hℓ hℓp n hn)
    push_cast at this
    split_ifs at this ⊢ with h <;> linear_combination this
  have hU' : ∀ n : ℕ, n ≠ 0 → ((af (n * p) : ℤ) : ZMod m) = (af n : ZMod m) := by
    intro n hn
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr (hU n hn)
    push_cast at this
    linear_combination this
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases Nat.lt_or_ge 1 n with h1 | h1
  swap
  ·
    have : n = 1 := by omega
    subst this
    rw [sigmaPrimeTo_one hp, Nat.cast_one, one_mul]
  ·
    set ℓ := n.minFac with hℓdef
    have hℓ : ℓ.Prime := Nat.minFac_prime (by omega)
    obtain ⟨n₀, hn₀⟩ : ℓ ∣ n := Nat.minFac_dvd n
    have hn₀0 : n₀ ≠ 0 := by rintro rfl; simp at hn₀; omega
    have hn₀lt : n₀ < n := by
      rw [hn₀]; exact lt_mul_left (Nat.pos_of_ne_zero hn₀0) hℓ.one_lt
    have hn_eq : n = n₀ * ℓ := by rw [hn₀, mul_comm]
    by_cases hℓp : ℓ = p
    ·
      subst hℓp
      rw [hn_eq, hU' n₀ hn₀0, ih n₀ (by omega) hn₀0, sigmaPrimeTo_mul_self hp hn₀0]
    ·
      have hrec := hT' ℓ hℓ hℓp n₀ hn₀0
      have hsig := sigmaPrimeTo_mul_prime hp hℓ hℓp hn₀0
      have ih₀ := ih n₀ (by omega) hn₀0
      rw [hn_eq]
      by_cases hd : ℓ ∣ n₀
      · have hq0 : n₀ / ℓ ≠ 0 := Nat.div_ne_zero_iff_of_dvd hd |>.mpr ⟨hn₀0, hℓ.ne_zero⟩
        have hqlt : n₀ / ℓ < n := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
        have ihq := ih (n₀ / ℓ) hqlt hq0
        rw [if_pos hd] at hrec hsig
        have hsig' := congrArg (Nat.cast : ℕ → ZMod m) hsig
        push_cast at hsig'
        linear_combination hrec + (1 + (ℓ : ZMod m)) * ih₀ - (ℓ : ZMod m) * ihq - (af 1 : ZMod m) * hsig'
      · rw [if_neg hd] at hrec hsig
        have hsig' := congrArg (Nat.cast : ℕ → ZMod m) hsig
        push_cast at hsig'
        linear_combination hrec + (1 + (ℓ : ZMod m)) * ih₀ - (af 1 : ZMod m) * hsig'

end S09A1U

theorem solution (p m : ℕ) [Fact p.Prime] (af : ℕ → ℤ) (hT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af (n * ℓ) + (if ℓ ∣ n then (ℓ : ℤ) * af (n / ℓ) else 0) - (1 + ℓ) * af n) (hU : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af (n * p) - af n) : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1 :=
  S09A1U.dvd_sub_sigmaPrimeTo_mul (Fact.out : p.Prime) m af hT hU

end S_ModularCurve_dvd_sub_sigmaPrimeTo_mul_of_eisenstein_eigen_mod
end P2MW
export P2MW.S_ModularCurve_dvd_sub_sigmaPrimeTo_mul_of_eisenstein_eigen_mod (solution)
