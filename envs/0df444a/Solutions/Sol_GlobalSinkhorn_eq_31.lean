-- Prove2me | solution 1 for GlobalSinkhorn.eq_31
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:46:51.77567+00:00
-- url     : https://prove2.me/submissions/c94d8a4c-7d57-4799-84ee-1e1a2c4f882d

import Mathlib
import Definitions.Def_GlobalSinkhorn_avg

open Matrix

open GlobalSinkhorn in
theorem solution {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) :
    GlobalSinkhorn.avg w ^ 2 * GlobalSinkhorn.avg (fun j => (w j)⁻¹) ^ 2 ≤
      (GlobalSinkhorn.avg (fun j => w j ^ 2) * GlobalSinkhorn.avg (fun j => (w j)⁻¹ ^ 2) + 1) / 2 := by
  unfold GlobalSinkhorn.avg
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (n : ℝ) := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast hn
  rw [← hN]
  obtain ⟨S1, hS1⟩ : ∃ S, S = ∑ j, w j := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S, S = ∑ j, (w j)⁻¹ := ⟨_, rfl⟩
  obtain ⟨Q1, hQ1⟩ : ∃ S, S = ∑ j, w j ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q2, hQ2⟩ : ∃ S, S = ∑ j, (w j)⁻¹ ^ 2 := ⟨_, rfl⟩
  rw [← hS1, ← hS2, ← hQ1, ← hQ2]
  have hcard : (∑ _j : Fin n, (1:ℝ)) = N := by simp [hN]
  have hinv : ∀ j, w j * (w j)⁻¹ = 1 := fun j => mul_inv_cancel₀ (hw j).ne'
  -- Cauchy–Schwarz facts
  have hS1p : 0 < S1 := by
    rw [hS1]; exact Finset.sum_pos (fun j _ => hw j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hS2p : 0 < S2 := by
    rw [hS2]; exact Finset.sum_pos (fun j _ => inv_pos.2 (hw j)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have F2 : N ^ 2 ≤ S1 * S2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => Real.sqrt (w j))
      (fun j => Real.sqrt ((w j)⁻¹))
    have e1 : ∀ j, Real.sqrt (w j) * Real.sqrt ((w j)⁻¹) = 1 := fun j => by
      rw [← Real.sqrt_mul (hw j).le, hinv, Real.sqrt_one]
    simp only [e1, Real.sq_sqrt (hw _).le, Real.sq_sqrt (inv_pos.2 (hw _)).le] at h
    rw [hcard, ← hS1, ← hS2] at h
    exact h
  obtain ⟨X, hX⟩ : ∃ X, X = N * Q1 - S1 ^ 2 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = N * Q2 - S2 ^ 2 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = S1 * S2 - N ^ 2 := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by rw [hZ]; linarith
  have hfg := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => N * w j - S1)
    (fun j => N * (w j)⁻¹ - S2)
  have e1 : ∑ j, (N * w j - S1) * (N * (w j)⁻¹ - S2) = N ^ 3 - N * S1 * S2 := by
    have h : ∀ j, (N * w j - S1) * (N * (w j)⁻¹ - S2) =
        N ^ 2 * 1 - (N * S2) * w j - (N * S1) * (w j)⁻¹ + S1 * S2 := fun j => by
      rw [← hinv j]; ring
    rw [Finset.sum_congr rfl (fun j _ => h j)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← hS1, ← hS2, ← hN]
    ring
  have e2 : ∑ j, (N * w j - S1) ^ 2 = N * X := by
    have h : ∀ j, (N * w j - S1) ^ 2 = N ^ 2 * w j ^ 2 - (2 * N * S1) * w j + S1 ^ 2 :=
      fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← hS1, ← hQ1, ← hN, hX]
    ring
  have e3 : ∑ j, (N * (w j)⁻¹ - S2) ^ 2 = N * Y := by
    have h : ∀ j, (N * (w j)⁻¹ - S2) ^ 2 = N ^ 2 * (w j)⁻¹ ^ 2 - (2 * N * S2) * (w j)⁻¹ + S2 ^ 2 :=
      fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← hS2, ← hQ2, ← hN, hY]
    ring
  rw [e1, e2, e3] at hfg
  have hX0 : 0 ≤ X := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (N * w j - S1))
    rw [e2] at this
    exact nonneg_of_mul_nonneg_right (by linarith) hN0
  have hY0 : 0 ≤ Y := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (N * (w j)⁻¹ - S2))
    rw [e3] at this
    exact nonneg_of_mul_nonneg_right (by linarith) hN0
  have hZZ : Z ^ 2 ≤ X * Y := by
    have : (N ^ 3 - N * S1 * S2) ^ 2 = N ^ 2 * Z ^ 2 := by rw [hZ]; ring
    rw [this] at hfg
    have h2 : N ^ 2 * Z ^ 2 ≤ N ^ 2 * (X * Y) := by
      calc N ^ 2 * Z ^ 2 ≤ N * X * (N * Y) := hfg
        _ = N ^ 2 * (X * Y) := by ring
    exact le_of_mul_le_mul_left h2 (by positivity)
  -- AM-GM step: 2 Z N^2 ≤ X S2^2 + Y S1^2
  have hAM : 2 * Z * N ^ 2 ≤ X * S2 ^ 2 + Y * S1 ^ 2 := by
    have hsq : (2 * Z * N ^ 2) ^ 2 ≤ (X * S2 ^ 2 + Y * S1 ^ 2) ^ 2 := by
      have h1 : (X * S2 ^ 2 + Y * S1 ^ 2) ^ 2 ≥ 4 * (X * Y) * (S1 * S2) ^ 2 := by
        nlinarith [sq_nonneg (X * S2 ^ 2 - Y * S1 ^ 2)]
      have h2 : (S1 * S2) ^ 2 ≥ (N ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) F2 2
      have h3 : 4 * (X * Y) * (S1 * S2) ^ 2 ≥ 4 * Z ^ 2 * (N ^ 2) ^ 2 := by
        have := mul_le_mul hZZ h2 (by positivity) (by positivity)
        linarith
      linarith
    have hpos : 0 ≤ X * S2 ^ 2 + Y * S1 ^ 2 := by positivity
    exact (pow_le_pow_iff_left₀ (by positivity) hpos two_ne_zero).1 hsq
  have hSS : S1 * S2 = Z + N ^ 2 := by rw [hZ]; ring
  have hSS2 : S1 ^ 2 * S2 ^ 2 = (Z + N ^ 2) ^ 2 := by rw [← hSS]; ring
  have hQ : Q1 * Q2 * N ^ 2 = (X + S1 ^ 2) * (Y + S2 ^ 2) := by rw [hX, hY]; ring
  have key : 2 * (S1 * S2) ^ 2 ≤ Q1 * Q2 * N ^ 2 + N ^ 4 := by
    rw [hQ, hSS]
    have hexp : (X + S1 ^ 2) * (Y + S2 ^ 2) + N ^ 4 - 2 * (Z + N ^ 2) ^ 2 =
        (X * Y - Z ^ 2) + (X * S2 ^ 2 + Y * S1 ^ 2 - 2 * Z * N ^ 2) +
          (S1 ^ 2 * S2 ^ 2 - (Z + N ^ 2) ^ 2) := by ring
    linarith [hexp, hZZ, hAM, hSS2]
  have e : (S1 / N) ^ 2 * (S2 / N) ^ 2 = (S1 * S2) ^ 2 / N ^ 4 := by
    field_simp <;> ring
  have e' : (Q1 / N * (Q2 / N) + 1) / 2 = (Q1 * Q2 * N ^ 2 + N ^ 4) / (2 * N ^ 4) := by
    field_simp <;> ring
  rw [e, e', div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_right key (pow_pos hN0 4).le
  linarith
