-- Prove2me | solution 1 for GoldenRatioVI.Fixed.norm_sq_identity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T16:16:00.043416+00:00
-- url     : https://prove2.me/submissions/7059a72f-2847-4882-9c06-df08517a0200

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_IsGRAALRun
open scoped goldenRatio


namespace GoldenRatioVI.Fixed

lemma z_formula {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z zbar : ℕ → E) (hbar : IsGoldenAveraging z zbar) (k : ℕ) :
    z (k + 1) = (1 + φ) • zbar (k + 1) - φ • zbar k := by
  have h := hbar (k + 1) (by omega)
  simp only [Nat.add_sub_cancel] at h
  have hφ : (φ : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  have hsq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  have h1 : φ • zbar (k + 1) = (φ - 1) • z (k + 1) + zbar k := by
    rw [h, smul_smul, mul_inv_cancel₀ hφ, one_smul]
  have h2 : z (k + 1) = φ • ((φ - 1) • z (k + 1)) := by
    rw [smul_smul]
    have : φ * (φ - 1) = 1 := by nlinarith
    rw [this, one_smul]
  rw [h2]
  have h3 : (φ - 1) • z (k + 1) = φ • zbar (k + 1) - zbar k := by
    rw [h1]; abel
  rw [h3, smul_sub, smul_smul, show φ * φ = 1 + φ by nlinarith]

theorem norm_sq_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z zbar : ℕ → E) (hbar : IsGoldenAveraging z zbar) (zs : E) (k : ℕ) :
    ‖z (k + 1) - zs‖ ^ 2 =
        (1 + φ) * ‖zbar (k + 1) - zs‖ ^ 2 - φ * ‖zbar k - zs‖ ^ 2
          + φ * (1 + φ) * ‖zbar (k + 1) - zbar k‖ ^ 2 ∧
      ‖z (k + 1) - zs‖ ^ 2 =
        (1 + φ) * ‖zbar (k + 1) - zs‖ ^ 2 - φ * ‖zbar k - zs‖ ^ 2
          + (1 / φ) * ‖z (k + 1) - zbar k‖ ^ 2 := by
  have hz := z_formula z zbar hbar k
  have hφ : (φ : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  have hsq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  set u := zbar (k + 1) - zs with hu
  set v := zbar k - zs with hv
  have e1 : z (k + 1) - zs = (1 + φ) • u - φ • v := by
    rw [hz, hu, hv]; module
  have e2 : zbar (k + 1) - zbar k = u - v := by rw [hu, hv]; abel
  have e3 : z (k + 1) - zbar k = (1 + φ) • (u - v) := by
    rw [hz, hu, hv]; module
  have n1 : ‖(1 + φ) • u - φ • v‖ ^ 2 =
      (1 + φ) ^ 2 * ‖u‖ ^ 2 - 2 * ((1 + φ) * φ) * inner ℝ u v + φ ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  have n2 : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2 := norm_sub_sq_real u v
  have n3 : ‖(1 + φ) • (u - v)‖ ^ 2 = (1 + φ) ^ 2 * ‖u - v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have part1 : ‖z (k + 1) - zs‖ ^ 2 = (1 + φ) * ‖u‖ ^ 2 - φ * ‖v‖ ^ 2
      + φ * (1 + φ) * ‖zbar (k + 1) - zbar k‖ ^ 2 := by
    rw [e1, e2, n1, n2]
    ring
  refine ⟨part1, ?_⟩
  rw [part1, e2, e3, n3]
  have hc : 1 / φ * (1 + φ) ^ 2 = φ * (1 + φ) := by
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff hφ]
    linear_combination (-(1 + φ)) * hsq
  rw [← mul_assoc, hc]

end GoldenRatioVI.Fixed

open GoldenRatioVI.Fixed

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z zbar : ℕ → E) (hbar : IsGoldenAveraging z zbar) (zs : E) (k : ℕ) :
    ‖z (k + 1) - zs‖ ^ 2 =
        (1 + φ) * ‖zbar (k + 1) - zs‖ ^ 2 - φ * ‖zbar k - zs‖ ^ 2
          + φ * (1 + φ) * ‖zbar (k + 1) - zbar k‖ ^ 2 ∧
      ‖z (k + 1) - zs‖ ^ 2 =
        (1 + φ) * ‖zbar (k + 1) - zs‖ ^ 2 - φ * ‖zbar k - zs‖ ^ 2
          + (1 / φ) * ‖z (k + 1) - zbar k‖ ^ 2 := by
  exact norm_sq_identity z zbar hbar zs k
