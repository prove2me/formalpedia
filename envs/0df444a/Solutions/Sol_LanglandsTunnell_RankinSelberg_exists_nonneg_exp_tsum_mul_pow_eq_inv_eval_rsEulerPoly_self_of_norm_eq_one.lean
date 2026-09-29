-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/949ed952-d4c4-57ae-87a6-a7e946a72360

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one

set_option autoImplicit false

open LanglandsTunnell.RankinSelberg

noncomputable section

namespace RS40LP

open Complex Polynomial

theorem eval_rsEulerPoly_roots (α₁ α₂ y : ℂ) (h₁ : α₁ ≠ 0) (h₂ : α₂ ≠ 0) :
    (rsEulerPoly ((α₁ + α₂) / (α₁ * α₂)) (α₁ * α₂)⁻¹ (α₁ + α₂) (α₁ * α₂) 0).eval y =
      (1 - y) ^ 2 * (1 - α₁ / α₂ * y) * (1 - α₂ / α₁ * y) := by
  simp only [rsEulerPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  field_simp
  ring

theorem lt_of_add_inv_lt {x N : ℝ} (hx : 0 < x) (hN : 1 ≤ N) (h : x + x⁻¹ < N + N⁻¹) : x < N := by
  by_contra hcon
  push Not at hcon
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have hxN : 1 ≤ x * N := by nlinarith
  have key : N + N⁻¹ ≤ x + x⁻¹ := by
    rw [← sub_nonneg]
    have : x + x⁻¹ - (N + N⁻¹) = (x - N) * (x * N - 1) / (x * N) := by
      field_simp
      ring
    rw [this]
    apply div_nonneg (mul_nonneg (sub_nonneg.2 hcon) (by linarith)) (by positivity)
  linarith

theorem real_pos_or_norm_eq_one {ρ : ℂ} (hρ : ρ ≠ 0) {s : ℝ} (hs : ρ + ρ⁻¹ = (s : ℂ)) (hs2 : -2 ≤ s) :
    (∃ r : ℝ, 0 < r ∧ ρ = (r : ℂ)) ∨ ‖ρ‖ = 1 := by
  by_cases h1 : ‖ρ‖ = 1
  · exact Or.inr h1
  left

  have hns : normSq ρ ≠ 0 := by rwa [Ne, normSq_eq_zero]
  have him : (ρ + ρ⁻¹).im = 0 := by rw [hs, ofReal_im]
  rw [add_im, inv_im] at him
  have hρim : ρ.im = 0 := by
    have hfac : ρ.im * (1 - (normSq ρ)⁻¹) = 0 := by
      have hnd : -ρ.im / normSq ρ = -(ρ.im / normSq ρ) := neg_div _ _
      rw [mul_sub, mul_one, ← div_eq_mul_inv]; linarith
    rcases mul_eq_zero.1 hfac with h | h
    · exact h
    · exfalso
      have hn1 : normSq ρ = 1 := by
        have := sub_eq_zero.1 h
        rw [eq_comm, inv_eq_one] at this
        exact this
      apply h1
      have : ‖ρ‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hn1
      nlinarith [norm_nonneg ρ]

  have hρre : ρ = ((ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hρim]
  have hre0 : ρ.re ≠ 0 := by
    intro h; apply hρ; rw [hρre, h, ofReal_zero]
  refine ⟨ρ.re, ?_, hρre⟩
  rcases lt_or_gt_of_ne hre0 with hneg | hpos
  · exfalso

    have hsr : s = ρ.re + (ρ.re)⁻¹ := by
      have := hs
      rw [hρre, ← ofReal_inv, ← ofReal_add, ofReal_inj] at this
      exact this.symm
    set r := ρ.re with hr
    have hle : r + r⁻¹ ≤ -2 := by
      have : r + r⁻¹ + 2 = (r + 1) ^ 2 / r := by field_simp; ring
      have h2 : (r + 1) ^ 2 / r ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hneg.le
      linarith
    have heq : r + r⁻¹ = -2 := le_antisymm hle (by rw [← hsr]; exact hs2)
    have hr1 : r = -1 := by
      have : (r + 1) ^ 2 = 0 := by
        have h3 : (r + 1) ^ 2 = (r + r⁻¹ + 2) * r := by field_simp; ring
        rw [h3, heq]; ring
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    apply h1
    rw [hρre, hr1]
    simp
  · exact hpos

theorem exists_real_pow_add_inv_pow {ρ : ℂ} (hρ : ρ ≠ 0)
    (hcase : (∃ r : ℝ, 0 < r ∧ ρ = (r : ℂ)) ∨ ‖ρ‖ = 1) (m : ℕ) :
    ∃ u : ℝ, ρ ^ m + ρ⁻¹ ^ m = (u : ℂ) ∧ -2 ≤ u ∧ u ≤ ‖ρ‖ ^ m + ‖ρ‖⁻¹ ^ m := by
  rcases hcase with ⟨r, hr, rfl⟩ | h1
  · refine ⟨r ^ m + r⁻¹ ^ m, by push_cast; ring, ?_, ?_⟩
    · have : 0 ≤ r ^ m + r⁻¹ ^ m := by positivity
      linarith
    · have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real]; exact abs_of_pos hr
      rw [hnr]
  ·
    have hinv : ρ⁻¹ = (starRingEnd ℂ) ρ := inv_eq_conj h1
    refine ⟨2 * (ρ ^ m).re, ?_, ?_, ?_⟩
    · rw [hinv, ← map_pow, Complex.add_conj]
    · have hb : |(ρ ^ m).re| ≤ ‖ρ ^ m‖ := Complex.abs_re_le_norm _
      rw [norm_pow, h1, one_pow] at hb
      have := neg_le_of_abs_le hb
      linarith
    · have hb : |(ρ ^ m).re| ≤ ‖ρ ^ m‖ := Complex.abs_re_le_norm _
      rw [norm_pow, h1, one_pow] at hb
      have := le_of_abs_le hb
      rw [h1, inv_one, one_pow]
      linarith

end RS40LP

open RS40LP Complex Polynomial in
theorem solution
    (a b : ℂ) (N : ℝ) (hN : 1 < N) (hb : ‖b‖ = 1) (hab : ∃ t : ℝ, 0 ≤ t ∧ a ^ 2 = (t : ℂ) * b)
    (ha : ‖a‖ ^ 2 < N + 2 + N⁻¹) :
    ∃ c : ℕ → ℝ, c 0 = 0 ∧ c 1 = ‖a‖ ^ 2 ∧ (∀ m : ℕ, 0 ≤ c m) ∧ (∀ m : ℕ, c m ≤ 4 * N ^ m) ∧
      ∀ y : ℂ, ‖y‖ < N⁻¹ →
        Summable (fun m : ℕ => (c m : ℂ) * y ^ m) ∧
        Complex.exp (∑' m : ℕ, (c m : ℂ) * y ^ m) = ((rsEulerPoly (a / b) b⁻¹ a b 0).eval y)⁻¹ := by
  obtain ⟨t, ht0, hat⟩ := hab
  have hb0 : b ≠ 0 := by
    intro h; rw [h, norm_zero] at hb; exact zero_ne_one hb
  have hN1 : (1 : ℝ) ≤ N := hN.le
  have hN0 : (0 : ℝ) < N := by linarith

  have hat2 : ‖a‖ ^ 2 = t := by
    rw [← norm_pow, hat, norm_mul, hb, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0]

  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (a ^ 2 - 4 * b) (n := 2) two_pos
  set α₁ : ℂ := (a + s) / 2 with hα₁
  set α₂ : ℂ := (a - s) / 2 with hα₂
  have hsum : α₁ + α₂ = a := by rw [hα₁, hα₂]; ring
  have hprod : α₁ * α₂ = b := by
    rw [hα₁, hα₂]
    have : (a + s) / 2 * ((a - s) / 2) = (a ^ 2 - s ^ 2) / 4 := by ring
    rw [this, hs]; ring
  have hα0 : α₁ ≠ 0 ∧ α₂ ≠ 0 := by
    rw [← not_or, ← mul_eq_zero, hprod]; exact hb0
  set ρ : ℂ := α₁ / α₂ with hρ
  have hρ0 : ρ ≠ 0 := div_ne_zero hα0.1 hα0.2
  have hρinv : ρ⁻¹ = α₂ / α₁ := by rw [hρ, inv_div]

  have hρsum : ρ + ρ⁻¹ = ((t - 2 : ℝ) : ℂ) := by
    have h1 : ρ + ρ⁻¹ = ((α₁ + α₂) ^ 2 - 2 * (α₁ * α₂)) / (α₁ * α₂) := by
      rw [hρinv, hρ]; field_simp; ring
    rw [h1, hsum, hprod, hat]; push_cast; field_simp; try ring
  have hcase := real_pos_or_norm_eq_one hρ0 hρsum (by linarith)

  have hρN : ‖ρ‖ < N ∧ ‖ρ‖⁻¹ < N := by
    rcases hcase with ⟨r, hr, hrρ⟩ | h1
    · have hnr : ‖ρ‖ = r := by rw [hrρ, Complex.norm_real]; exact abs_of_pos hr
      have hrs : r + r⁻¹ = t - 2 := by
        have := hρsum; rw [hrρ, ← ofReal_inv, ← ofReal_add, ofReal_inj] at this; exact this
      have hlt : r + r⁻¹ < N + N⁻¹ := by rw [hrs, ← hat2]; linarith
      have hlt' : r⁻¹ + r⁻¹⁻¹ < N + N⁻¹ := by rw [inv_inv, add_comm]; exact hlt
      rw [hnr]
      exact ⟨lt_of_add_inv_lt hr hN1 hlt, lt_of_add_inv_lt (inv_pos.2 hr) hN1 hlt'⟩
    · rw [h1, inv_one]; exact ⟨hN, hN⟩

  choose u hu using fun m => exists_real_pow_add_inv_pow hρ0 hcase m
  refine ⟨fun m => (2 + u m) / m, by simp, ?_, ?_, ?_, ?_⟩
  ·
    have h1 := (hu 1).1
    rw [pow_one, pow_one, hρsum, ofReal_inj] at h1
    simp only [Nat.cast_one, div_one]
    rw [← h1, hat2]; ring
  · intro m
    exact div_nonneg (by linarith [(hu m).2.1]) (Nat.cast_nonneg m)
  · intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have hNm : (1 : ℝ) ≤ N ^ m := one_le_pow₀ hN1
    have hb1 : ‖ρ‖ ^ m ≤ N ^ m := pow_le_pow_left₀ (norm_nonneg _) hρN.1.le m
    have hb2 : ‖ρ‖⁻¹ ^ m ≤ N ^ m := pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg _)) hρN.2.le m
    have hum : u m ≤ 2 * N ^ m := by linarith [(hu m).2.2]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    calc (2 + u m) / m ≤ (2 + u m) / 1 := by
          apply div_le_div_of_nonneg_left (by linarith [(hu m).2.1]) one_pos hm1
      _ ≤ 4 * N ^ m := by rw [div_one]; linarith
  · intro y hy
    have hy1 : ‖y‖ < 1 := lt_of_lt_of_le hy (inv_le_one_of_one_le₀ hN1)
    have hρy : ‖ρ * y‖ < 1 := by
      rw [norm_mul]
      calc ‖ρ‖ * ‖y‖ ≤ N * ‖y‖ := by gcongr; exact hρN.1.le
        _ < N * N⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hN0.ne'
    have hρy' : ‖ρ⁻¹ * y‖ < 1 := by
      rw [norm_mul, norm_inv]
      calc ‖ρ‖⁻¹ * ‖y‖ ≤ N * ‖y‖ := by gcongr; exact hρN.2.le
        _ < N * N⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hN0.ne'
    have h1 := hasSum_taylorSeries_neg_log hy1
    have h2 := hasSum_taylorSeries_neg_log hρy
    have h3 := hasSum_taylorSeries_neg_log hρy'
    have hsum3 := ((h1.mul_left 2).add h2).add h3
    have hterm : ∀ n : ℕ, (((2 + u n) / n : ℝ) : ℂ) * y ^ n =
        2 * (y ^ n / n) + (ρ * y) ^ n / n + (ρ⁻¹ * y) ^ n / n := by
      intro n
      have hun := (hu n).1
      push_cast
      rw [← hun, mul_pow, mul_pow]
      ring
    have hS : HasSum (fun n : ℕ => (((2 + u n) / n : ℝ) : ℂ) * y ^ n)
        (2 * -Complex.log (1 - y) + -Complex.log (1 - ρ * y) + -Complex.log (1 - ρ⁻¹ * y)) := by
      convert hsum3 using 1 <;> first | rfl | (funext n; exact hterm n)
    refine ⟨hS.summable, ?_⟩
    rw [hS.tsum_eq]

    have hne : ∀ z : ℂ, ‖z‖ < 1 → (1 - z) ≠ 0 := by
      intro z hz h
      have : z = 1 := (sub_eq_zero.1 h).symm
      rw [this, norm_one] at hz; exact lt_irrefl _ hz
    have e1 : Complex.exp (2 * -Complex.log (1 - y) + -Complex.log (1 - ρ * y) + -Complex.log (1 - ρ⁻¹ * y)) =
        ((1 - y) ^ 2 * (1 - ρ * y) * (1 - ρ⁻¹ * y))⁻¹ := by
      rw [Complex.exp_add, Complex.exp_add, show (2 : ℂ) * -Complex.log (1 - y) =
        -Complex.log (1 - y) + -Complex.log (1 - y) by ring, Complex.exp_add, Complex.exp_neg, Complex.exp_neg,
        Complex.exp_neg, Complex.exp_log (hne y hy1), Complex.exp_log (hne _ hρy), Complex.exp_log (hne _ hρy')]
      field_simp
    rw [e1]
    congr 1

    have := eval_rsEulerPoly_roots α₁ α₂ y hα0.1 hα0.2
    rw [hsum, hprod] at this
    rw [this, hρinv, hρ]

end
end S_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one (solution)
