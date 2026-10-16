-- Prove2me | solution 1 for OAI.ShortEgyptian.phase_sum_first_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:07:31.743615+00:00
-- url     : https://prove2.me/submissions/0d7da7f7-7618-4a4f-a608-3f24d33ad6ad

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/FirstDerivative.lean:L132-L198
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.phase_sum_first_derivative. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Theorems.Thm_OAI_ShortEgyptian_phase_increment_inv

-- ---- from OAI.NumberTheory.ShortEgyptian.FirstDerivative ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem phase_sub_one_norm (x : ℝ) : ‖phase x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  have hsq : ‖phase x - 1‖ ^ 2 = (2 * |Real.sin (Real.pi * x)|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, phase_re, Complex.sub_im,
      Complex.one_im, phase_im, sub_zero]
    rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring,
      Real.sin_two_mul, Real.cos_two_mul]
    have hh := Real.sin_sq_add_cos_sq (Real.pi * x)
    rw [mul_pow, sq_abs]
    nlinarith [sq_nonneg (Real.cos (Real.pi * x) ^ 2 - 1)]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hsq

theorem sin_pi_lower {β x : ℝ} (hβ : 0 ≤ β) (hx : β ≤ x) (hx' : x ≤ 1 - β) :
    2 * β ≤ Real.sin (Real.pi * x) := by
  have hx0 : 0 ≤ x := le_trans hβ hx
  have hx1 : x ≤ 1 := by linarith
  by_cases hh : x ≤ 1 / 2
  · have h := Real.mul_le_sin (x := Real.pi * x) (by positivity)
      (by nlinarith [Real.pi_pos])
    have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    rw [heq] at h
    linarith
  · have h := Real.mul_le_sin (x := Real.pi * (1 - x)) (by positivity)
      (by nlinarith [Real.pi_pos])
    have heq : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    rw [heq, show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring,
      Real.sin_pi_sub] at h
    linarith

theorem phase_increment_im_mono :
    MonotoneOn (fun x : ℝ => ((phase x - 1)⁻¹).im) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  dsimp only
  rw [phase_increment_inv hx0 hx1, phase_increment_inv hy0 hy1]
  simp only [Complex.sub_im, Complex.div_im, Complex.neg_im, Complex.one_im,
    Complex.neg_re, Complex.one_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  have hsx : 0 < Real.sin (Real.pi * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hsy : 0 < Real.sin (Real.pi * y) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hd := Real.sin_nonneg_of_nonneg_of_le_pi (x := Real.pi * y - Real.pi * x)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  rw [Real.sin_sub] at hd
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.sin (Real.pi * y))
    (by positivity : 0 < 2 * Real.sin (Real.pi * x))).mpr
  nlinarith

theorem summation_by_parts_differences (a b : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ range N, b n * (a (n + 1) - a n)) =
      b N * a N - b 0 * a 0 - ∑ n ∈ range N, (b (n + 1) - b n) * a (n + 1) := by
  have heq (n : ℕ) : b n * (a (n + 1) - a n) =
      (b (n + 1) * a (n + 1) - b n * a n) -
        (b (n + 1) - b n) * a (n + 1) := by ring
  simp_rw [heq]
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun n => b n * a n)]

theorem vertical_variation (b : ℕ → ℂ) (N : ℕ)
    (hre : ∀ n ≤ N, (b n).re = (b 0).re)
    (him : ∀ n < N, (b n).im ≤ (b (n + 1)).im) :
    (∑ n ∈ range N, ‖b (n + 1) - b n‖) = (b N).im - (b 0).im := by
  have hnorm (n : ℕ) (hn : n ∈ range N) :
      ‖b (n + 1) - b n‖ = (b (n + 1)).im - (b n).im := by
    have hn' := Finset.mem_range.mp hn
    rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.sub_re, Complex.sub_im,
      hre (n + 1) (by omega), hre n (by omega), sub_self, zero_pow (by norm_num), zero_add,
      Real.sqrt_sq (sub_nonneg.mpr (him n hn'))]
  rw [Finset.sum_congr rfl hnorm]
  exact Finset.sum_range_sub (fun n => (b n).im) N

theorem phase_sum_first_derivative {β : ℝ} (hβ : 0 < β)
    (f : ℕ → ℝ) (q : ℤ) (N : ℕ)
    (hlow : ∀ n ≤ N, β ≤ f (n + 1) - f n - q)
    (hupp : ∀ n ≤ N, f (n + 1) - f n - q ≤ 1 - β)
    (hmono : ∀ n < N, f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) :
    ‖∑ n ∈ range N, phase (f n)‖ ≤ 1 / β := by
  let d (n : ℕ) : ℝ := f (n + 1) - f n - q
  let b (n : ℕ) : ℂ := (phase (d n) - 1)⁻¹
  have hd0 (n : ℕ) (hn : n ≤ N) : 0 < d n := lt_of_lt_of_le hβ (hlow n hn)
  have hd1 (n : ℕ) (hn : n ≤ N) : d n < 1 := lt_of_le_of_lt (hupp n hn) (by linarith)
  have hb (n : ℕ) (hn : n ≤ N) : ‖b n‖ ≤ 1 / (4 * β) := by
    have hs := sin_pi_lower hβ.le (hlow n hn) (hupp n hn)
    have hnorm : 4 * β ≤ ‖phase (d n) - 1‖ := by
      rw [phase_sub_one_norm, abs_of_nonneg (by linarith : 0 ≤ Real.sin (Real.pi * d n))]
      linarith
    dsimp only [b]
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hnorm
  have hne (n : ℕ) (hn : n ≤ N) : phase (d n) - 1 ≠ 0 := by
    intro hh
    have hs := sin_pi_lower hβ.le (hlow n hn) (hupp n hn)
    have hn0 := phase_sub_one_norm (d n)
    rw [hh, norm_zero] at hn0
    have habs := le_abs_self (Real.sin (Real.pi * d n))
    linarith
  have hre (n : ℕ) (hn : n ≤ N) : (b n).re = (-1 / 2 : ℝ) := by
    dsimp only [b]
    rw [phase_increment_inv (hd0 n hn) (hd1 n hn)]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
  have him (n : ℕ) (hn : n < N) : (b n).im ≤ (b (n + 1)).im := by
    apply phase_increment_im_mono ⟨hd0 n (by omega), hd1 n (by omega)⟩
      ⟨hd0 (n + 1) (by omega), hd1 (n + 1) (by omega)⟩
    dsimp [d]
    linarith [hmono n hn]
  have hrel (n : ℕ) (hn : n ∈ range N) :
      b n * (phase (f (n + 1)) - phase (f n)) = phase (f n) := by
    have heq : f (n + 1) = f n + d n + q := by dsimp [d]; ring
    rw [heq, phase_add, phase_add, phase_int, mul_one]
    dsimp only [b]
    rw [show phase (f n) * phase (d n) - phase (f n) =
        (phase (d n) - 1) * phase (f n) by ring,
      ← mul_assoc, inv_mul_cancel₀ (hne n (by simpa using (mem_range.mp hn).le)), one_mul]
  have heq := summation_by_parts_differences (fun n => phase (f n)) b N
  rw [Finset.sum_congr rfl hrel] at heq
  have hv := vertical_variation b N (fun n hn => (hre n hn).trans (hre 0 (by omega)).symm) him
  have hvle : (∑ n ∈ range N, ‖b (n + 1) - b n‖) ≤ 2 / (4 * β) := by
    rw [hv]
    have h1 := Complex.im_le_norm (b N)
    have h0 := Complex.abs_im_le_norm (b 0)
    have h0' := neg_le_abs (b 0).im
    have hadd : 1 / (4 * β) + 1 / (4 * β) = 2 / (4 * β) := by ring
    linarith [hb N le_rfl, hb 0 (by omega)]
  have hs : ‖∑ n ∈ range N, (b (n + 1) - b n) * phase (f (n + 1))‖ ≤
      2 / (4 * β) := by
    calc
      _ ≤ ∑ n ∈ range N, ‖(b (n + 1) - b n) * phase (f (n + 1))‖ := norm_sum_le _ _
      _ = ∑ n ∈ range N, ‖b (n + 1) - b n‖ := by simp
      _ ≤ _ := hvle
  rw [heq]
  have hn := norm_sub_le (b N * phase (f N) - b 0 * phase (f 0))
    (∑ n ∈ range N, (b (n + 1) - b n) * phase (f (n + 1)))
  have hn' := norm_sub_le (b N * phase (f N)) (b 0 * phase (f 0))
  simp only [norm_mul, phase_norm, mul_one] at hn'
  have hsum : 1 / (4 * β) + 1 / (4 * β) + 2 / (4 * β) = 1 / β := by ring
  linarith [hb N le_rfl, hb 0 (by omega)]

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.phase_sum_first_derivative := @_root_.OAI.ShortEgyptian.phase_sum_first_derivative
