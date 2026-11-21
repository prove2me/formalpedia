-- Prove2me | solution 2 for MasulloGRH.quasinuclear_of_hilbertian_two_summing_chain
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:33:32.715537+00:00
-- url     : https://prove2.me/submissions/a33e9bd5-dbfc-4577-a849-de002b2ace93

import Theorems.Thm_MasulloGRH_hilbertian_two_summing_bessel_expansion
import Theorems.Thm_MasulloGRH_two_summing_dual_hilbertSchmidt_weights

set_option autoImplicit false

open MasulloGRH

universe u

theorem solution (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (h₁ h₂ h₃ : Seminorm ℂ E) (hc₃ : Continuous h₃)
    (hpar₁ : ∀ x y, h₁ (x + y) ^ 2 + h₁ (x - y) ^ 2 = 2 * h₁ x ^ 2 + 2 * h₁ y ^ 2)
    (hpar₂ : ∀ x y, h₂ (x + y) ^ 2 + h₂ (x - y) ^ 2 = 2 * h₂ x ^ 2 + 2 * h₂ y ^ 2)
    (hpar₃ : ∀ x y, h₃ (x + y) ^ 2 + h₃ (x - y) ^ 2 = 2 * h₃ x ^ 2 + 2 * h₃ y ^ 2)
    (h₁₂ : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ h₂ y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
      ∑ i, h₁ (x i) ^ 2 ≤ c)
    (h₂₃ : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ h₃ y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
      ∑ i, h₂ (x i) ^ 2 ≤ c) :
    ∃ (f : ℕ → StrongDual ℂ E) (c : ℕ → ℝ),
      (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ h₃ x) ∧
      ∀ x, h₁ x ≤ ∑' n, c n * ‖f n x‖ := by
  have hle : ∀ x, h₂ x ≤ h₃ x := by
    intro x
    have h := h₂₃ 1 (fun _ => x) (h₃ x ^ 2) (by
      intro f hf
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact pow_le_pow_left₀ (norm_nonneg _) (hf x) 2)
    simp only [Finset.univ_unique, Finset.sum_singleton] at h
    exact (pow_le_pow_iff_left₀ (apply_nonneg _ _) (apply_nonneg _ _) two_ne_zero).1 h
  obtain ⟨g, b, hb0, hb2, hg, hexp⟩ :=
    hilbertian_two_summing_bessel_expansion E hE h₁ h₂ h₃ hc₃ hle hpar₁ hpar₂ h₁₂
  obtain ⟨a, ha0, ha2, hga⟩ :=
    two_summing_dual_hilbertSchmidt_weights E hE h₂ h₃ hc₃ hpar₂ hpar₃ h₂₃ g hg
  classical
  refine ⟨fun n => if a n = 0 then 0 else ((a n : ℂ)⁻¹) • g n, fun n => a n * b n,
    fun n => mul_nonneg (ha0 n) (hb0 n), ?_, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun n => mul_nonneg (ha0 n) (hb0 n))
      (fun n => ?_) ((ha2.add hb2).div_const 2)
    nlinarith [sq_nonneg (a n - b n)]
  · intro n x
    by_cases h : a n = 0
    · simp [h]
    · have hpos : 0 < a n := lt_of_le_of_ne (ha0 n) (Ne.symm h)
      simp only [h, if_false, ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul,
        norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      rw [inv_mul_le_iff₀ hpos]
      exact hga n x
  · intro x
    refine (hexp x).trans (le_of_eq (tsum_congr fun n => ?_))
    by_cases h : a n = 0
    · have : ‖g n x‖ = 0 := le_antisymm (by simpa [h] using hga n x) (norm_nonneg _)
      simp [h, this]
    · have hpos : 0 < a n := lt_of_le_of_ne (ha0 n) (Ne.symm h)
      simp only [h, if_false, ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul,
        norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      field_simp
