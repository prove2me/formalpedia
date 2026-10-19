-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteEntropy.js_le_tv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:45:43.113993+00:00
-- url     : https://prove2.me/submissions/65177edc-f475-4fa8-9f7c-2f02005cd278

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory
theorem h43_hlow (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - |2*t-1|) * Real.log 2 ≤ Real.binEntropy t := by
  have hc := Real.strictConcave_binEntropy.concaveOn
  rcases le_total t (1/2) with h | h
  · have := hc.2 (show (0:ℝ) ∈ Set.Icc 0 1 by simp) (show (2⁻¹:ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
      (show (0:ℝ) ≤ 1 - 2*t by linarith) (show (0:ℝ) ≤ 2*t by linarith) (show (1 - 2*t) + 2*t = 1 by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.binEntropy_zero, Real.binEntropy_two_inv] at this
    rw [show 2 * t * 2⁻¹ = t by ring] at this
    rw [abs_of_nonpos (by linarith)]; linarith
  · have := hc.2 (show (2⁻¹:ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) (show (1:ℝ) ∈ Set.Icc 0 1 by simp)
      (show (0:ℝ) ≤ 2 - 2*t by linarith) (show (0:ℝ) ≤ 2*t - 1 by linarith) (show (2 - 2*t) + (2*t - 1) = 1 by ring)
    simp only [smul_eq_mul, mul_one, Real.binEntropy_one, Real.binEntropy_two_inv, mul_zero, add_zero] at this
    rw [show (2 - 2 * t) * 2⁻¹ + (2 * t - 1) = t by ring] at this
    rw [abs_of_nonneg (by linarith)]; linarith

theorem h43_pt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog ((a+b)/2) - (Real.negMulLog a + Real.negMulLog b)/2 ≤ |a-b|/2 * Real.log 2 := by
  rcases (show (0:ℝ) ≤ a + b from add_nonneg ha hb).eq_or_lt with h0 | h0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0; simp
  set S := a + b with hS
  set t := a / S with ht
  have hat : a = S * t := by rw [ht]; field_simp
  have hbt : b = S * (1 - t) := by rw [ht]; field_simp; ring
  have h1 : Real.negMulLog a = t * Real.negMulLog S + S * Real.negMulLog t := by
    rw [hat, Real.negMulLog_mul]
  have h2 : Real.negMulLog b = (1-t) * Real.negMulLog S + S * Real.negMulLog (1-t) := by
    rw [hbt, Real.negMulLog_mul]
  have h3 : Real.negMulLog ((a+b)/2) = 2⁻¹ * Real.negMulLog S + S * (2⁻¹ * Real.log 2) := by
    rw [← hS, show S / 2 = S * 2⁻¹ by ring, Real.negMulLog_mul]
    congr 2; rw [Real.negMulLog, Real.log_inv]; ring
  have hab : |a - b| = S * |2*t-1| := by
    rw [show a - b = S * (2*t-1) by rw [hat, hbt]; ring, abs_mul, abs_of_pos h0]
  have ht0 : 0 ≤ t := div_nonneg ha h0.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one h0]; linarith
  have hh := h43_hlow t ht0 ht1
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub] at hh
  rw [h1, h2, h3, hab]
  nlinarith [mul_le_mul_of_nonneg_left hh h0.le]

theorem solution {α : Type uα} [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) :
    js s p q ≤ totalVariation s p q*Real.log 2 := by
  unfold js totalVariation entropy
  have key : ∑ a ∈ s, (Real.negMulLog ((p a + q a)/2) - (Real.negMulLog (p a) + Real.negMulLog (q a))/2)
      ≤ ∑ a ∈ s, |p a - q a|/2 * Real.log 2 :=
    Finset.sum_le_sum fun a ha => h43_pt (p a) (q a) (hp a ha) (hq a ha)
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div] at key
  exact key

