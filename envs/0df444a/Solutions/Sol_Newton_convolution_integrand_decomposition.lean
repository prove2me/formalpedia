-- Prove2me | solution 1 for Newton.convolution_integrand_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:22:42.872033+00:00
-- url     : https://prove2.me/submissions/27cfc34d-cf47-4de1-a1a3-0e6ea173b640

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
import Theorems.Thm_Newton_young_exponent_p_le_r
import Theorems.Thm_Newton_young_exponent_q_le_r

set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f g : (Fin n → ℝ) → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hp_ne_top : p ≠ ⊤) (hq_ne_top : q ≠ ⊤) (hr_ne_top : r ≠ ⊤)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (x y : Fin n → ℝ) :
    ‖f y‖ * ‖g (x - y)‖ =
      (‖f y‖^(p/r).toReal * ‖g (x - y)‖^(q/r).toReal) *
      ‖f y‖^(1 - p/r).toReal *
      ‖g (x - y)‖^(1 - q/r).toReal := by
  -- Notation for the two nonnegative numbers we decompose.
  set a : ℝ := ‖f y‖ with ha_def
  set b : ℝ := ‖g (x - y)‖ with hb_def
  have ha_nonneg : 0 ≤ a := by simp [ha_def]
  have hb_nonneg : 0 ≤ b := by simp [hb_def]
  -- Positivity of p, q, r and finiteness of 1/p, 1/q.
  have hp_pos' : 0 < p := one_pos.trans_le hp
  have hq_pos' : 0 < q := one_pos.trans_le hq
  have hp_pos : p ≠ 0 := hp_pos'.ne'
  have hq_pos : q ≠ 0 := hq_pos'.ne'
  have h_one_div_p_ne_top : 1/p ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.one_ne_top hp_pos
  have h_one_div_q_ne_top : 1/q ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.one_ne_top hq_pos
  -- Show that r is positive: otherwise 1/p + 1/q would be infinite.
  have hr_ne_zero : r ≠ 0 := by
    by_contra hr0
    have h1 : (1 : ℝ≥0∞) / r = ⊤ := by simp [hr0]
    have h2 : 1 + (1 : ℝ≥0∞) / r = ⊤ := by simp [h1]
    have h3 : 1/p + 1/q = ⊤ := by
      calc 1/p + 1/q = 1 + 1/r := hpqr
        _ = ⊤ := h2
    have h_fin : 1/p + 1/q ≠ (⊤ : ℝ≥0∞) :=
      ENNReal.add_ne_top.mpr ⟨h_one_div_p_ne_top, h_one_div_q_ne_top⟩
    exact h_fin h3
  -- From the Young exponent condition we know p ≤ r and q ≤ r.
  have h_p_le_r : p ≤ r := young_exponent_p_le_r hq hpqr
  have h_q_le_r : q ≤ r := young_exponent_q_le_r hp hpqr
  -- Hence p/r ≤ 1 and q/r ≤ 1.
  have hp_div_le_one : p / r ≤ 1 := by
    have := (ENNReal.div_le_iff_le_mul (a := p) (b := r) (c := 1)
        (hb0 := Or.inl hr_ne_zero) (hbt := Or.inl hr_ne_top))
    -- `this` is an iff; use the → direction.
    exact this.mpr (by simpa [one_mul] using h_p_le_r)
  have hq_div_le_one : q / r ≤ 1 := by
    have := (ENNReal.div_le_iff_le_mul (a := q) (b := r) (c := 1)
        (hb0 := Or.inl hr_ne_zero) (hbt := Or.inl hr_ne_top))
    exact this.mpr (by simpa [one_mul] using h_q_le_r)
  -- In ℝ≥0∞ we have p/r + (1 - p/r) = 1 and similarly for q.
  have h_p_decomp : p / r + (1 - p / r) = 1 :=
    add_tsub_cancel_of_le hp_div_le_one
  have h_q_decomp : q / r + (1 - q / r) = 1 :=
    add_tsub_cancel_of_le hq_div_le_one
  -- The fractions p/r, q/r, 1 - p/r, 1 - q/r are all finite.
  have hp_div_ne_top : p / r ≠ ⊤ :=
    ENNReal.div_ne_top hp_ne_top hr_ne_zero
  have hq_div_ne_top : q / r ≠ ⊤ :=
    ENNReal.div_ne_top hq_ne_top hr_ne_zero
  have h_one_sub_p_ne_top : 1 - p / r ≠ ⊤ := by
    -- It is bounded by 1.
    have : 1 - p / r ≤ (1 : ℝ≥0∞) := by
      exact tsub_le_self
    exact ne_of_lt (lt_of_le_of_lt this (by simp))
  have h_one_sub_q_ne_top : 1 - q / r ≠ ⊤ := by
    have : 1 - q / r ≤ (1 : ℝ≥0∞) := by
      exact tsub_le_self
    exact ne_of_lt (lt_of_le_of_lt this (by simp))
  -- Convert the ENNReal equalities to equalities of real exponents.
  have h_sum_p :
      (p/r).toReal + (1 - p/r).toReal = 1 := by
    have h := (ENNReal.toReal_add (a := p / r) (b := 1 - p / r)
        hp_div_ne_top h_one_sub_p_ne_top).symm
    -- h : (p/r).toReal + (1 - p/r).toReal = (p/r + (1 - p/r)).toReal
    simpa [h_p_decomp, ENNReal.toReal_one] using h
  have h_sum_q :
      (q/r).toReal + (1 - q/r).toReal = 1 := by
    have h := (ENNReal.toReal_add (a := q / r) (b := 1 - q / r)
        hq_div_ne_top h_one_sub_q_ne_top).symm
    simpa [h_q_decomp, ENNReal.toReal_one] using h
  -- Now work purely in ℝ with the nonnegative numbers `a` and `b`.
  -- Convert (p/r).toReal to p.toReal / r.toReal
  have h_p_div_toReal : (p/r).toReal = p.toReal / r.toReal :=
    ENNReal.toReal_div p r
  have h_q_div_toReal : (q/r).toReal = q.toReal / r.toReal :=
    ENNReal.toReal_div q r
  have h_a :
      a ^ (p/r).toReal * a ^ (1 - p/r).toReal = a := by
    have h_rpow :=
      Real.rpow_add_of_nonneg ha_nonneg (ENNReal.toReal_nonneg (a := p/r))
        (ENNReal.toReal_nonneg (a := 1 - p/r))
    -- h_rpow : a ^ ((p/r).toReal + (1 - p/r).toReal)
    --            = a ^ (p/r).toReal * a ^ (1 - p/r).toReal
    have : a ^ (p/r).toReal * a ^ (1 - p/r).toReal =
        a ^ ((p/r).toReal + (1 - p/r).toReal) := by
      simpa [mul_comm] using h_rpow.symm
    -- Replace the exponent by 1.
    simp only [this, h_sum_p, Real.rpow_one]
  have h_b :
      b ^ (q/r).toReal * b ^ (1 - q/r).toReal = b := by
    have h_rpow :=
      Real.rpow_add_of_nonneg hb_nonneg (ENNReal.toReal_nonneg (a := q/r))
        (ENNReal.toReal_nonneg (a := 1 - q/r))
    have : b ^ (q/r).toReal * b ^ (1 - q/r).toReal =
        b ^ ((q/r).toReal + (1 - q/r).toReal) := by
      simpa [mul_comm] using h_rpow.symm
    simp only [this, h_sum_q, Real.rpow_one]
  -- Put everything together.
  -- First rewrite both sides in terms of `a` and `b`.
  have hab : ‖f y‖ * ‖g (x - y)‖ = a * b := by
    simp [ha_def, hb_def]
  -- Rewrite `h_a` and `h_b` in terms of `p.toReal / r.toReal`.
  have h_a' : a ^ (p.toReal / r.toReal) * a ^ (1 - p/r).toReal = a := by
    rw [← h_p_div_toReal]; exact h_a
  have h_b' : b ^ (q.toReal / r.toReal) * b ^ (1 - q/r).toReal = b := by
    rw [← h_q_div_toReal]; exact h_b
  -- Rewrite the right-hand side.
  have hrhs : a * b =
      (a^(p.toReal / r.toReal) * b^(q.toReal / r.toReal)) *
      a^(1 - p/r).toReal * b^(1 - q/r).toReal := by
    -- Rearrange the factors and use the identities `h_a'` and `h_b'`.
    calc
      a * b = (a ^ (p.toReal / r.toReal) * a ^ (1 - p/r).toReal) *
              (b ^ (q.toReal / r.toReal) * b ^ (1 - q/r).toReal) := by
                simp [h_a', h_b']
      _ = (a^(p.toReal / r.toReal) * b^(q.toReal / r.toReal)) *
          a^(1 - p/r).toReal * b^(1 - q/r).toReal := by
                ring_nf
  -- Conclude, rewriting back in terms of norms.
  simp only [ha_def, hb_def] at hrhs
  rw [h_p_div_toReal, h_q_div_toReal]
  exact hrhs
end Newton
