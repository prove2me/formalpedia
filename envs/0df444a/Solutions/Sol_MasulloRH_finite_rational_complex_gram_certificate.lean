-- Prove2me | solution 1 for MasulloRH.finite_rational_complex_gram_certificate
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T15:02:13.582165+00:00
-- url     : https://prove2.me/submissions/6a2dbd20-faf4-45c0-9d34-14d4818442e7

import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open scoped BigOperators ComplexConjugate

private theorem rational_complex_approx (z : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℚ × ℚ, ‖z - ((r.1 : ℂ) + (r.2 : ℂ) * Complex.I)‖ ≤ ε := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn
    (show z.re - ε / 2 < z.re + ε / 2 by linarith)
  obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn
    (show z.im - ε / 2 < z.im + ε / 2 by linarith)
  refine ⟨(a, b), ?_⟩
  have ha : |z.re - (a : ℝ)| < ε / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hb : |z.im - (b : ℝ)| < ε / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have h := Complex.norm_le_abs_re_add_abs_im
    (z - ((a : ℂ) + (b : ℂ) * Complex.I))
  simp only [Complex.sub_re, Complex.add_re, Complex.ratCast_re, Complex.mul_re,
    Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im,
    mul_one, zero_add] at h
  linarith

private theorem quadratic_form_entry_error {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (G Q : ι → ι → ℂ) (η : ℝ)
    (hentry : ∀ i j, ‖G i j - Q i j‖ ≤ η) :
    (∑ i, ∑ j, conj (d i) * d j * Q i j).re ≤
      (∑ i, ∑ j, conj (d i) * d j * G i j).re +
        η * (∑ i, (|(d i).re| + |(d i).im|)) ^ 2 := by
  classical
  let a : ι → ℝ := fun i => |(d i).re| + |(d i).im|
  have ha (i : ι) : 0 ≤ a i := by dsimp [a]; positivity
  have hd (i : ι) : ‖d i‖ ≤ a i := Complex.norm_le_abs_re_add_abs_im _
  have hp (i j : ι) :
      ‖conj (d i) * d j * (Q i j - G i j)‖ ≤ η * (a i * a j) := by
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_conj]
    have he : ‖Q i j - G i j‖ ≤ η := by simpa only [norm_sub_rev] using hentry i j
    calc
      ‖d i‖ * ‖d j‖ * ‖Q i j - G i j‖
          ≤ (a i * a j) * η :=
            mul_le_mul (mul_le_mul (hd i) (hd j) (norm_nonneg _) (ha i)) he
              (norm_nonneg _) (mul_nonneg (ha i) (ha j))
      _ = η * (a i * a j) := by ring
  have hn : ‖∑ i, ∑ j, conj (d i) * d j * (Q i j - G i j)‖ ≤
      η * (∑ i, a i) ^ 2 := by
    calc
      ‖∑ i, ∑ j, conj (d i) * d j * (Q i j - G i j)‖
          ≤ ∑ i, ‖∑ j, conj (d i) * d j * (Q i j - G i j)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖conj (d i) * d j * (Q i j - G i j)‖ :=
        Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, η * (a i * a j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hp i j
      _ = η * (∑ i, a i) ^ 2 := by
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul]
        ring
  have hr := Complex.re_le_norm
    (∑ i, ∑ j, conj (d i) * d j * (Q i j - G i j))
  have heq : (∑ i, ∑ j, conj (d i) * d j * (Q i j - G i j)) =
      (∑ i, ∑ j, conj (d i) * d j * Q i j) -
        (∑ i, ∑ j, conj (d i) * d j * G i j) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [heq, Complex.sub_re] at hr
  rw [heq] at hn
  dsimp [a] at hn
  linarith

theorem solution {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (G : ι → ι → ℂ) (b : ℝ)
    (hgap : (∑ i, ∑ j, conj (d i) * d j * G i j).re < b) :
    ∃ (R : ι → ι → ℚ × ℚ) (η : ℚ), 0 ≤ η ∧
      (∀ i j, ‖G i j - (((R i j).1 : ℂ) + ((R i j).2 : ℂ) * Complex.I)‖ ≤ (η : ℝ)) ∧
      (∑ i, ∑ j, conj (d i) * d j *
        (((R i j).1 : ℂ) + ((R i j).2 : ℂ) * Complex.I)).re +
        (η : ℝ) * (∑ i, (|(d i).re| + |(d i).im|)) ^ 2 < b := by
  classical
  let S : ℝ := ∑ i, (|(d i).re| + |(d i).im|)
  let g : ℝ := (∑ i, ∑ j, conj (d i) * d j * G i j).re
  have hm : 0 < b - g := by dsimp [g]; linarith
  have hden : 0 < 2 * (S ^ 2 + 1) := by positivity
  obtain ⟨η, hη₀, hη₁⟩ := exists_rat_btwn (div_pos hm hden)
  have hη : (0 : ℝ) < (η : ℝ) := by simpa using hη₀
  have hsmall : 2 * (η : ℝ) * (S ^ 2 + 1) < b - g := by
    have h := (lt_div_iff₀ hden).mp hη₁
    nlinarith
  let R : ι → ι → ℚ × ℚ := fun i j =>
    (rational_complex_approx (G i j) (η : ℝ) hη).choose
  have hR (i j : ι) :
      ‖G i j - (((R i j).1 : ℂ) + ((R i j).2 : ℂ) * Complex.I)‖ ≤ (η : ℝ) :=
    (rational_complex_approx (G i j) (η : ℝ) hη).choose_spec
  refine ⟨R, η, ?_, hR, ?_⟩
  · exact_mod_cast hη.le
  · have hbound := quadratic_form_entry_error d G
      (fun i j => (((R i j).1 : ℂ) + ((R i j).2 : ℂ) * Complex.I)) (η : ℝ) hR
    change _ ≤ g + (η : ℝ) * S ^ 2 at hbound
    change _ + (η : ℝ) * S ^ 2 < b
    nlinarith
