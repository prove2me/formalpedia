-- Prove2me | solution 1 for MomentSearch.theorem_24
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T22:59:16.28418+00:00
-- url     : https://prove2.me/submissions/b5cdd41a-7c9c-4f8a-a3e5-285a6210f8fd

import Mathlib
import Theorems.Thm_MomentSearch_rakhmanov_interpolation_kernel
import Theorems.Thm_MomentSearch_rakhmanov_grid_kernel_sum

theorem solution :
    ∃ C₀ : ℝ, ∀ N κ : ℕ, 1 ≤ κ → κ < N →
      ∀ Q : Polynomial ℝ, Q.natDegree ≤ κ →
      (∀ j : ℕ, 1 ≤ j → j ≤ N → |Q.eval (-1 + (2 * (j : ℝ) - 1) / (N : ℝ))| ≤ 1) →
      ∀ r : ℝ, r = Real.sqrt (1 - (κ : ℝ) ^ 2 / (N : ℝ) ^ 2) →
      ∀ x : ℝ, -r < x → x < r →
        |Q.eval x| ≤
          C₀ * Real.logb 2
            (Real.pi / Real.arctan ((N : ℝ) / (κ : ℝ) * Real.sqrt (r ^ 2 - x ^ 2))) := by
  obtain ⟨A, hA, hkernel⟩ := MomentSearch.rakhmanov_interpolation_kernel
  obtain ⟨D, hD, hsum⟩ := MomentSearch.rakhmanov_grid_kernel_sum
  refine ⟨A * D, ?_⟩
  intro N k hk hkN P hP hgrid r hr x hx₁ hx₂
  obtain ⟨M, y, hM, hMN, hxy, hdensity, hbound⟩ :=
    hkernel N k hk hkN P hP hgrid r hr x hx₁ hx₂
  have hN : 0 < N := by omega
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hkr : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hrad : 0 < r ^ 2 - x ^ 2 := by
    have hprod : 0 < (r - x) * (r + x) :=
      mul_pos (sub_pos.mpr hx₂) (by linarith)
    nlinarith only [hprod]
  let θ := Real.arctan ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - x ^ 2))
  have hθ : 0 < θ := Real.arctan_pos.mpr
    (mul_pos (div_pos hNr hkr) (Real.sqrt_pos.mpr hrad))
  let μ := (N : ℝ) / Real.pi * θ
  have hμ : 0 < μ := mul_pos (div_pos hNr Real.pi_pos) hθ
  have hμM : μ ≤ M := hdensity
  have hratio : (N : ℝ) / M ≤ (N : ℝ) / μ :=
    div_le_div_of_nonneg_left hNr.le hμ hμM
  have heq : (N : ℝ) / μ = Real.pi / θ := by
    dsimp [μ]
    field_simp [hNr.ne', hθ.ne', Real.pi_ne_zero]
  have hlog : Real.logb 2 ((N : ℝ) / M) ≤ Real.logb 2 (Real.pi / θ) := by
    rw [← heq]
    exact Real.logb_le_logb_of_le (by norm_num) (div_pos hNr hM) hratio
  calc
    _ ≤ A * (∑ j ∈ Finset.Icc 1 N,
          1 / (max 1 ((N : ℝ) * |(-1 + (2 * (j : ℝ) - 1) / (N : ℝ)) - x|) *
            max 1 (M * |(-1 + (2 * (j : ℝ) - 1) / (N : ℝ)) - y|))) := hbound
    _ ≤ A * (D * Real.logb 2 ((N : ℝ) / M)) :=
      mul_le_mul_of_nonneg_left (hsum N hN M x y hM hMN hxy) hA.le
    _ ≤ (A * D) * Real.logb 2 (Real.pi / θ) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hD.le) hA.le
