-- Prove2me | solution 1 for LamLitt.coeff_denominator_bound_of_integrality
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T23:19:50.487809+00:00
-- url     : https://prove2.me/submissions/d5b6b0de-22fd-49f0-a0f4-5474a70b4ce5

import Definitions.Def_LamLitt_Defs
import Theorems.Thm_LamLitt_factorial_mul_coeff_denominator_bound
import Mathlib

set_option autoImplicit false

namespace LamLittAuxS2

/-- If `c * x` is an integer then `x.den ∣ c`. -/
theorem den_dvd_of_mul_eq_int (x : ℚ) (c : ℕ) (m : ℤ) (h : (c : ℚ) * x = (m : ℚ)) :
    x.den ∣ c := by
  have h1 : (c : ℚ) * (x.num : ℚ) = (m : ℚ) * (x.den : ℚ) := by
    have hx : (x.num : ℚ) = x * (x.den : ℚ) := (Rat.mul_den_eq_num x).symm
    rw [hx, ← mul_assoc, h]
  have h2 : (c : ℤ) * x.num = m * (x.den : ℤ) := by exact_mod_cast h1
  have h3 : (x.den : ℤ) ∣ (c : ℤ) * x.num := ⟨m, by rw [h2, mul_comm]⟩
  have hcop : IsCoprime (x.den : ℤ) x.num := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact x.reduced
  exact Int.natCast_dvd_natCast.mp (hcop.dvd_of_dvd_mul_right h3)

/-- If `x.den ∣ c` then `c * x` is an integer. -/
theorem exists_int_of_den_dvd (x : ℚ) (c : ℕ) (h : x.den ∣ c) :
    ∃ m : ℤ, (c : ℚ) * x = (m : ℚ) := by
  obtain ⟨e, rfl⟩ := h
  refine ⟨(e : ℤ) * x.num, ?_⟩
  have hx : (x.num : ℚ) = x * (x.den : ℚ) := (Rat.mul_den_eq_num x).symm
  push_cast
  rw [hx]
  ring

/-- Elements of `ℤ[0]` are integers. -/
theorem int_of_mem_adjoin_zero (x : ℚ) (hx : x ∈ Algebra.adjoin ℤ {(0 : ℚ)}) :
    ∃ t : ℤ, x = (t : ℚ) := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, by simp [hy]⟩
  | algebraMap r => exact ⟨r, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    exact ⟨s + t, by push_cast; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    exact ⟨s * t, by push_cast; ring⟩

/-- Elements of `ℤ[1/N]` (`N ≠ 0`) become integers after multiplying by a power of `N`. -/
theorem pow_mul_int_of_mem_adjoin (N : ℕ) (hN : N ≠ 0) (x : ℚ)
    (hx : x ∈ Algebra.adjoin ℤ {(1 / N : ℚ)}) :
    ∃ j : ℕ, ∃ t : ℤ, (N : ℚ) ^ j * x = (t : ℚ) := by
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨1, 1, by field_simp; simp⟩
  | algebraMap r => exact ⟨0, r, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨j₁, s, hs⟩ := ha
    obtain ⟨j₂, t, ht⟩ := hb
    refine ⟨j₁ + j₂, s * (N : ℤ) ^ j₂ + t * (N : ℤ) ^ j₁, ?_⟩
    push_cast
    rw [← hs, ← ht]
    ring
  | mul a b _ _ ha hb =>
    obtain ⟨j₁, s, hs⟩ := ha
    obtain ⟨j₂, t, ht⟩ := hb
    refine ⟨j₁ + j₂, s * t, ?_⟩
    push_cast
    rw [← hs, ← ht]
    ring

/-- The arithmetic core: a common divisor of `N ^ j` and `D ^ (k+1) * k!` divides
`(D * N) ^ (k+1)`. -/
theorem dvd_mul_pow (D N j k d : ℕ) (hD : D ≠ 0) (hN : N ≠ 0)
    (h1 : d ∣ N ^ j) (h2 : d ∣ D ^ (k + 1) * k.factorial) :
    d ∣ (D * N) ^ (k + 1) := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p e hp hpe
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he; simp
  have hpd : p ∣ d := dvd_trans (dvd_pow_self p (Nat.pos_iff_ne_zero.mp he)) hpe
  have hpN : p ∣ N := hp.dvd_of_dvd_pow (dvd_trans hpd h1)
  have hvN : 1 ≤ padicValNat p N := one_le_padicValNat_of_dvd hN hpN
  have hDk : D ^ (k + 1) * k.factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hD) (Nat.factorial_ne_zero k)
  have hDN : (D * N) ^ (k + 1) ≠ 0 := pow_ne_zero _ (mul_ne_zero hD hN)
  have hle : e ≤ padicValNat p (D ^ (k + 1) * k.factorial) :=
    (padicValNat_dvd_iff_le hDk).mp (dvd_trans hpe h2)
  rw [padicValNat.mul (pow_ne_zero _ hD) (Nat.factorial_ne_zero k), padicValNat.pow] at hle
  have hfac : padicValNat p k.factorial ≤ k := padicValNat_factorial_le (p := p) k
  rw [padicValNat_dvd_iff_le hDN, padicValNat.pow, padicValNat.mul hD hN]
  nlinarith [hle, hfac, hvN]

end LamLittAuxS2

open LamLitt PowerSeries in
theorem solution {n : ℕ} (f : PowerSeries ℚ)
    (g : MvRatFunc (Fin (n + 1)) ℚ) (hODE : IsSolutionOfAlgebraicODE n f g)
    (N : ℕ) (hN : IsCoeffIntegralAdjointInvNat f N) :
    ∃ M : ℕ, 0 < M ∧ ∀ k : ℕ, ∃ m : ℤ,
      (M : ℚ) ^ (k + 1) * PowerSeries.coeff k f = (m : ℚ) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    refine ⟨1, Nat.one_pos, fun k => ?_⟩
    have hk := hN k
    unfold ℤAdjoinInvNat at hk
    have h0 : (1 / ((0 : ℕ) : ℚ)) = 0 := by simp
    rw [h0] at hk
    obtain ⟨t, ht⟩ := LamLittAuxS2.int_of_mem_adjoin_zero _ hk
    exact ⟨t, by rw [ht]; simp⟩
  · obtain ⟨D, hDpos, hD⟩ := LamLitt.factorial_mul_coeff_denominator_bound f g hODE
    refine ⟨D * N, Nat.mul_pos hDpos hNpos, fun k => ?_⟩
    have hk := hN k
    unfold ℤAdjoinInvNat at hk
    obtain ⟨j, t, ht⟩ :=
      LamLittAuxS2.pow_mul_int_of_mem_adjoin N (Nat.pos_iff_ne_zero.mp hNpos) _ hk
    obtain ⟨m, hm⟩ := hD k
    have h1 : (PowerSeries.coeff k f).den ∣ N ^ j :=
      LamLittAuxS2.den_dvd_of_mul_eq_int _ (N ^ j) t (by push_cast; exact ht)
    have h2 : (PowerSeries.coeff k f).den ∣ D ^ (k + 1) * k.factorial :=
      LamLittAuxS2.den_dvd_of_mul_eq_int _ (D ^ (k + 1) * k.factorial) m
        (by push_cast; rw [mul_assoc]; exact hm)
    have h3 := LamLittAuxS2.dvd_mul_pow D N j k _ (Nat.pos_iff_ne_zero.mp hDpos)
      (Nat.pos_iff_ne_zero.mp hNpos) h1 h2
    obtain ⟨m', hm'⟩ := LamLittAuxS2.exists_int_of_den_dvd _ _ h3
    exact ⟨m', by rw [← hm']; push_cast; ring⟩
