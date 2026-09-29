-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_one_sub_mul_std_mul_contragredient_mul_eval_rsEulerPoly_self_of_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d0c73aff-eebc-5dc7-8c55-49f4a776841a

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

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_one_sub_mul_std_mul_contragredient_mul_eval_rsEulerPoly_self_of_norm_eq_one

set_option autoImplicit false

open LanglandsTunnell.RankinSelberg

noncomputable section

namespace LOCPOS9

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

end LOCPOS9

open LOCPOS9 Complex Polynomial in
theorem solution
    (a b : ℂ) (N : ℝ) (hN : 1 < N) (hb : ‖b‖ = 1) (hab : ∃ t : ℝ, 0 ≤ t ∧ a ^ 2 = (t : ℂ) * b)
    (ha : ‖a‖ ^ 2 < N + 2 + N⁻¹) :
    ∃ c : ℕ → ℝ, c 0 = 0 ∧ (∀ m : ℕ, 0 ≤ c m) ∧ (∀ m : ℕ, c m ≤ 9 * N ^ m) ∧
      ∀ y : ℂ, ‖y‖ < N⁻¹ →
        Summable (fun m : ℕ => (c m : ℂ) * y ^ m) ∧
        Complex.exp (∑' m : ℕ, (c m : ℂ) * y ^ m) =
          ((1 - y) * (1 - a * y + b * y ^ 2) * (1 - (a / b) * y + b⁻¹ * y ^ 2) *
            (rsEulerPoly (a / b) b⁻¹ a b 0).eval y)⁻¹ := by
  obtain ⟨t, ht0, hat⟩ := hab
  have hb0 : b ≠ 0 := by
    intro h; rw [h, norm_zero] at hb; exact zero_ne_one hb
  have hN1 : (1 : ℝ) ≤ N := hN.le
  have hN0 : (0 : ℝ) < N := by linarith
  have hat2 : ‖a‖ ^ 2 = t := by
    rw [← norm_pow, hat, norm_mul, hb, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0]

  have hconjb : (starRingEnd ℂ) b = b⁻¹ := (Complex.inv_eq_conj hb).symm
  have hconja : (starRingEnd ℂ) a = a / b := by
    by_cases ha0 : a = 0
    · simp [ha0]
    · have h1 : a * (starRingEnd ℂ) a = (t : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hat2]
      have h2 : (starRingEnd ℂ) a = (t : ℂ) / a := by
        rw [eq_div_iff ha0, mul_comm]; exact h1
      have ht' : (t : ℂ) = a ^ 2 / b := by
        rw [hat, mul_div_cancel_right₀ _ hb0]
      rw [h2, ht']
      field_simp

  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (a ^ 2 - 4 * b) (n := 2) two_pos
  obtain ⟨α₁, hα₁⟩ : ∃ α₁ : ℂ, α₁ = (a + s) / 2 := ⟨_, rfl⟩
  obtain ⟨α₂, hα₂⟩ : ∃ α₂ : ℂ, α₂ = (a - s) / 2 := ⟨_, rfl⟩
  have hsum : α₁ + α₂ = a := by rw [hα₁, hα₂]; ring
  have hprod : α₁ * α₂ = b := by
    rw [hα₁, hα₂]
    have : (a + s) / 2 * ((a - s) / 2) = (a ^ 2 - s ^ 2) / 4 := by ring
    rw [this, hs]; ring
  have hα0 : α₁ ≠ 0 ∧ α₂ ≠ 0 := by
    rw [← not_or, ← mul_eq_zero, hprod]; exact hb0
  have hA1 : α₁ ≠ 0 := hα0.1
  have hA2 : α₂ ≠ 0 := hα0.2
  clear hα₁ hα₂
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℂ, ρ = α₁ / α₂ := ⟨_, rfl⟩
  have hρ0 : ρ ≠ 0 := by rw [hρ]; exact div_ne_zero hA1 hA2
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

  have hα₁sq : ‖α₁‖ ^ 2 = ‖ρ‖ := by
    have : α₁ ^ 2 = ρ * b := by rw [hρ, ← hprod]; field_simp
    rw [← norm_pow, this, norm_mul, hb, mul_one]
  have hα₂sq : ‖α₂‖ ^ 2 = ‖ρ‖⁻¹ := by
    have : α₂ ^ 2 = ρ⁻¹ * b := by rw [hρinv, ← hprod]; field_simp
    rw [← norm_pow, this, norm_mul, hb, mul_one, norm_inv]
  have hα₁N : ‖α₁‖ ^ 2 < N := by rw [hα₁sq]; exact hρN.1
  have hα₂N : ‖α₂‖ ^ 2 < N := by rw [hα₂sq]; exact hρN.2
  have hα₁iN : ‖α₁⁻¹‖ ^ 2 < N := by rw [norm_inv, inv_pow, hα₁sq]; exact hρN.2
  have hα₂iN : ‖α₂⁻¹‖ ^ 2 < N := by rw [norm_inv, inv_pow, hα₂sq, inv_inv]; exact hρN.1

  have hinvsum : α₁⁻¹ + α₂⁻¹ = (starRingEnd ℂ) α₁ + (starRingEnd ℂ) α₂ := by
    rw [← map_add, hsum, hconja, ← hsum, ← hprod]; field_simp; ring
  have hinvprod : α₁⁻¹ * α₂⁻¹ = (starRingEnd ℂ) α₁ * (starRingEnd ℂ) α₂ := by
    rw [← map_mul, hprod, hconjb, ← hprod, mul_inv]
  have newton : ∀ (x y u v : ℂ), x + y = u + v → x * y = u * v → ∀ m : ℕ, x ^ m + y ^ m = u ^ m + v ^ m := by
    intro x y u v h1 h2 m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      match m with
      | 0 => simp
      | 1 => simpa using h1
      | m + 2 =>
        have r : ∀ p q : ℂ, p ^ (m + 2) + q ^ (m + 2) = (p + q) * (p ^ (m + 1) + q ^ (m + 1)) - (p * q) * (p ^ m + q ^ m) := by
          intro p q; ring
        rw [r x y, r u v, h1, h2, ih (m + 1) (by omega), ih m (by omega)]
  have hS' : ∀ m : ℕ, (starRingEnd ℂ) (α₁ ^ m) + (starRingEnd ℂ) (α₂ ^ m) = α₁⁻¹ ^ m + α₂⁻¹ ^ m := by
    intro m
    rw [map_pow, map_pow]
    exact (newton _ _ _ _ hinvsum hinvprod m).symm
  have hSS' : ∀ m : ℕ, (α₁ ^ m + α₂ ^ m) * (α₁⁻¹ ^ m + α₂⁻¹ ^ m) = 2 + ρ ^ m + ρ⁻¹ ^ m := by
    intro m
    have h1 : α₁ ^ m ≠ 0 := pow_ne_zero _ hA1
    have h2 : α₂ ^ m ≠ 0 := pow_ne_zero _ hA2
    rw [hρinv, hρ, div_pow, div_pow, inv_pow, inv_pow]
    field_simp
    ring

  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ m, c m = ‖1 + α₁ ^ m + α₂ ^ m‖ ^ 2 / m := ⟨_, fun _ => rfl⟩
  have hcm : ∀ m : ℕ, ((c m : ℝ) : ℂ) =
      (3 + (α₁ ^ m + α₂ ^ m) + (α₁⁻¹ ^ m + α₂⁻¹ ^ m) + (ρ ^ m + ρ⁻¹ ^ m)) / m := by
    intro m
    have hnsq : ((‖1 + α₁ ^ m + α₂ ^ m‖ : ℝ) : ℂ) ^ 2 =
        (1 + α₁ ^ m + α₂ ^ m) * (1 + (α₁⁻¹ ^ m + α₂⁻¹ ^ m)) := by
      rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_add, map_add,
        map_one]
      congr 1
      rw [add_assoc, hS' m]
    rw [hc m]
    push_cast
    rw [hnsq]
    congr 1
    linear_combination hSS' m
  refine ⟨c, by simp [hc], fun m => by rw [hc]; positivity, ?_, ?_⟩
  ·
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hc]
    have hNm : (1 : ℝ) ≤ N ^ m := one_le_pow₀ hN1
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hA : (‖α₁‖ ^ m) ^ 2 ≤ N ^ m := by
      rw [← pow_mul, mul_comm, pow_mul]; exact pow_le_pow_left₀ (sq_nonneg _) hα₁N.le m
    have hB : (‖α₂‖ ^ m) ^ 2 ≤ N ^ m := by
      rw [← pow_mul, mul_comm, pow_mul]; exact pow_le_pow_left₀ (sq_nonneg _) hα₂N.le m
    have htri : ‖1 + α₁ ^ m + α₂ ^ m‖ ≤ 1 + ‖α₁‖ ^ m + ‖α₂‖ ^ m := by
      calc ‖1 + α₁ ^ m + α₂ ^ m‖ ≤ ‖1 + α₁ ^ m‖ + ‖α₂ ^ m‖ := norm_add_le _ _
        _ ≤ (‖(1 : ℂ)‖ + ‖α₁ ^ m‖) + ‖α₂ ^ m‖ := by gcongr; exact norm_add_le _ _
        _ = 1 + ‖α₁‖ ^ m + ‖α₂‖ ^ m := by rw [norm_one, norm_pow, norm_pow]
    have hA0 : 0 ≤ ‖α₁‖ ^ m := by positivity
    have hB0 : 0 ≤ ‖α₂‖ ^ m := by positivity
    have hsq : ‖1 + α₁ ^ m + α₂ ^ m‖ ^ 2 ≤ (1 + ‖α₁‖ ^ m + ‖α₂‖ ^ m) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hkey : (1 + ‖α₁‖ ^ m + ‖α₂‖ ^ m) ^ 2 ≤ 9 * N ^ m := by
      nlinarith [sq_nonneg (1 - ‖α₁‖ ^ m), sq_nonneg (1 - ‖α₂‖ ^ m), sq_nonneg (‖α₁‖ ^ m - ‖α₂‖ ^ m)]
    calc c m = ‖1 + α₁ ^ m + α₂ ^ m‖ ^ 2 / m := hc m
      _ ≤ ‖1 + α₁ ^ m + α₂ ^ m‖ ^ 2 / 1 := div_le_div_of_nonneg_left (sq_nonneg _) one_pos hm1
      _ ≤ 9 * N ^ m := by rw [div_one]; exact hsq.trans hkey
  ·
    intro y hy
    have hy1 : ‖y‖ < 1 := lt_of_lt_of_le hy (inv_le_one_of_one_le₀ hN1)
    have hyN : ‖y‖ ^ 2 < N⁻¹ ^ 2 := pow_lt_pow_left₀ hy (norm_nonneg _) two_ne_zero
    have small : ∀ w : ℂ, ‖w‖ ^ 2 < N → ‖w * y‖ < 1 := by
      intro w hw
      have h2 : ‖w * y‖ ^ 2 < 1 := by
        rw [norm_mul, mul_pow]
        calc ‖w‖ ^ 2 * ‖y‖ ^ 2 ≤ N * ‖y‖ ^ 2 := by gcongr
          _ < N * N⁻¹ ^ 2 := by gcongr
          _ = N⁻¹ := by field_simp
          _ ≤ 1 := inv_le_one_of_one_le₀ hN1
      exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
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
    have s1 := small α₁ hα₁N
    have s2 := small α₂ hα₂N
    have s3 := small α₁⁻¹ hα₁iN
    have s4 := small α₂⁻¹ hα₂iN
    have L0 := hasSum_taylorSeries_neg_log hy1
    have L1 := hasSum_taylorSeries_neg_log s1
    have L2 := hasSum_taylorSeries_neg_log s2
    have L3 := hasSum_taylorSeries_neg_log s3
    have L4 := hasSum_taylorSeries_neg_log s4
    have L5 := hasSum_taylorSeries_neg_log hρy
    have L6 := hasSum_taylorSeries_neg_log hρy'
    have hsum9 := (((((((L0.add L0).add L0).add L1).add L2).add L3).add L4).add L5).add L6
    have hS : HasSum (fun n : ℕ => ((c n : ℝ) : ℂ) * y ^ n)
        (-Complex.log (1 - y) + -Complex.log (1 - y) + -Complex.log (1 - y)
          + -Complex.log (1 - α₁ * y) + -Complex.log (1 - α₂ * y)
          + -Complex.log (1 - α₁⁻¹ * y) + -Complex.log (1 - α₂⁻¹ * y)
          + -Complex.log (1 - ρ * y) + -Complex.log (1 - ρ⁻¹ * y)) := by
      convert hsum9 using 1
      funext n
      rw [hcm n]
      simp only [mul_pow]
      ring
    refine ⟨hS.summable, ?_⟩
    rw [hS.tsum_eq]
    have hne : ∀ z : ℂ, ‖z‖ < 1 → (1 - z) ≠ 0 := by
      intro z hz h
      have : z = 1 := (sub_eq_zero.1 h).symm
      rw [this, norm_one] at hz; exact lt_irrefl _ hz
    simp only [Complex.exp_add, Complex.exp_neg]
    rw [Complex.exp_log (hne y hy1), Complex.exp_log (hne _ s1), Complex.exp_log (hne _ s2),
      Complex.exp_log (hne _ s3), Complex.exp_log (hne _ s4), Complex.exp_log (hne _ hρy),
      Complex.exp_log (hne _ hρy')]

    have eP := eval_rsEulerPoly_roots α₁ α₂ y hA1 hA2
    rw [hsum, hprod] at eP
    have eQ : (1 - y) * (1 - a * y + b * y ^ 2) * (1 - a / b * y + b⁻¹ * y ^ 2) *
        (rsEulerPoly (a / b) b⁻¹ a b 0).eval y
        = (1 - y) * (1 - y) * (1 - y) * (1 - α₁ * y) * (1 - α₂ * y) * (1 - α₁⁻¹ * y) * (1 - α₂⁻¹ * y)
          * (1 - ρ * y) * (1 - ρ⁻¹ * y) := by
      rw [eP, hρinv, hρ, ← hsum, ← hprod]
      field_simp
      ring
    rw [eQ]
    simp only [mul_inv]

end
end S_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_one_sub_mul_std_mul_contragredient_mul_eval_rsEulerPoly_self_of_norm_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_one_sub_mul_std_mul_contragredient_mul_eval_rsEulerPoly_self_of_norm_eq_one (solution)
