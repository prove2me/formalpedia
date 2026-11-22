-- Prove2me | solution 1 for LamLitt.exp_pow_sharpness
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T23:26:19.807986+00:00
-- url     : https://prove2.me/submissions/0e99b508-2d1b-4f99-8b76-0f6c0491be17

import Definitions.Def_LamLitt_Defs
import Theorems.Thm_LamLitt_eisenstein
import Mathlib

set_option autoImplicit false

open PowerSeries

namespace LamLittAuxA

open LamLitt in
theorem den_coprime_of_mem (N : ℕ) (x : ℚ) (hx : x ∈ ℤAdjoinInvNat N) :
    ∀ p : ℕ, p.Prime → N < p → Nat.Coprime x.den p := by
  unfold ℤAdjoinInvNat at hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    subst hy
    intro p hp hNp
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp
    · rw [one_div, Rat.inv_natCast_den, if_neg (Nat.pos_iff_ne_zero.mp hpos)]
      exact Nat.Coprime.symm
        ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hpos hNp))
  | algebraMap r =>
    intro p hp hNp
    simp
  | add a b _ _ ha hb =>
    intro p hp hNp
    exact Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd a b)
      (Nat.Coprime.mul_left (ha p hp hNp) (hb p hp hNp))
  | mul a b _ _ ha hb =>
    intro p hp hNp
    exact Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd a b)
      (Nat.Coprime.mul_left (ha p hp hNp) (hb p hp hNp))

theorem ode_identity (m : ℕ) (hm : 0 < m) (f : PowerSeries ℚ)
    (hf : ∀ k : ℕ, coeff k f = if m ∣ k then ((k / m).factorial : ℚ)⁻¹ else 0) :
    derivative ℚ f = PowerSeries.C (m : ℚ) * PowerSeries.X ^ (m - 1) * f := by
  ext k
  rw [coeff_derivative, mul_assoc, coeff_C_mul, coeff_X_pow_mul', hf]
  by_cases h : m ∣ k + 1
  · obtain ⟨j, hj⟩ := h
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0; omega
      · exact h0
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hk : k = m * i + (m - 1) := by
      have : m * (i + 1) = m * i + m := by ring
      omega
    have hle : m - 1 ≤ k := by omega
    have hsub : k - (m - 1) = m * i := by omega
    rw [if_pos ⟨i + 1, hj⟩, if_pos hle, hf, hsub, if_pos (dvd_mul_right m i), hj,
      Nat.mul_div_cancel_left _ hm, Nat.mul_div_cancel_left _ hm, Nat.factorial_succ]
    have hi : ((i.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have hk1 : ((k : ℚ) + 1) = (m : ℚ) * ((i : ℚ) + 1) := by exact_mod_cast hj
    rw [hk1]
    push_cast
    have hi1 : ((i : ℚ) + 1) ≠ 0 := by positivity
    field_simp
  · rw [if_neg h, zero_mul]
    by_cases hle : m - 1 ≤ k
    · rw [if_pos hle, hf, if_neg, mul_zero]
      intro hd
      apply h
      have : k + 1 = (k - (m - 1)) + m := by omega
      rw [this]
      exact Dvd.dvd.add hd (dvd_refl m)
    · rw [if_neg hle, mul_zero]

theorem coeff_den_coprime (m : ℕ) (f : PowerSeries ℚ)
    (hf : ∀ k : ℕ, coeff k f = if m ∣ k then ((k / m).factorial : ℚ)⁻¹ else 0)
    (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : k < m * p) : Nat.Coprime (coeff k f).den p := by
  rw [hf]
  by_cases h : m ∣ k
  · rw [if_pos h, Rat.inv_natCast_den, if_neg (Nat.factorial_ne_zero _)]
    have hlt : k / m < p := Nat.div_lt_of_lt_mul hk
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
      (fun hd => absurd ((Nat.Prime.dvd_factorial hp).1 hd) (not_le.2 hlt)))
  · rw [if_neg h]; simp

open LamLitt in
theorem not_integral (m : ℕ) (hm : 0 < m) (f : PowerSeries ℚ)
    (hf : ∀ k : ℕ, coeff k f = if m ∣ k then ((k / m).factorial : ℚ)⁻¹ else 0) :
    ¬ ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N := by
  rintro ⟨N, hN⟩
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes (N + 1)
  have h := den_coprime_of_mem N _ (hN (m * p)) p hp (by omega)
  rw [hf, if_pos (dvd_mul_right m p), Nat.mul_div_cancel_left _ hm, Rat.inv_natCast_den,
    if_neg (Nat.factorial_ne_zero _)] at h
  have hd : p ∣ p.factorial := (Nat.Prime.dvd_factorial hp).2 le_rfl
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 h.symm hd

end LamLittAuxA

open LamLitt PowerSeries in
theorem solution (m : ℕ) (hm : 0 < m) (f : PowerSeries ℚ)
    (hf : ∀ k : ℕ, PowerSeries.coeff k f = if m ∣ k then ((k / m).factorial : ℚ)⁻¹ else 0) :
    IsSolutionOfAlgebraicODE 1 f
        (algebraMap (MvPolynomial (Fin (1 + 1)) ℚ) (MvRatFunc (Fin (1 + 1)) ℚ)
          (MvPolynomial.C (m : ℚ) * MvPolynomial.X 0 ^ (m - 1) * MvPolynomial.X 1)) ∧
      (∀ p : Nat.Primes, ∀ k : ℕ, k < m * (p : ℕ) → Nat.Coprime (PowerSeries.coeff k f).den p) ∧
      (¬ ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N) ∧
      ¬ IsAlgebraic (Polynomial ℚ) f := by
  refine ⟨?_, fun p k hk => LamLittAuxA.coeff_den_coprime m f hf p p.prop k hk,
    LamLittAuxA.not_integral m hm f hf,
    fun hAlg => LamLittAuxA.not_integral m hm f hf (LamLitt.eisenstein f hAlg)⟩
  refine ⟨MvPolynomial.C (m : ℚ) * MvPolynomial.X 0 ^ (m - 1) * MvPolynomial.X 1, 1, ?_, ?_, ?_⟩
  · rw [map_one, div_one]
  · rw [map_one]; exact one_ne_zero
  · have h1 : (1 : Fin (1 + 1)) = Fin.succ 0 := rfl
    rw [map_one, mul_one, map_mul, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      MvPolynomial.aeval_X, h1, Fin.cases_succ, Fin.cases_zero]
    exact LamLittAuxA.ode_identity m hm f hf
