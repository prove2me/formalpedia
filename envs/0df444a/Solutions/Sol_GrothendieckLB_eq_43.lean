-- Prove2me | solution 1 for GrothendieckLB.eq_43
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:29:44.56161+00:00
-- url     : https://prove2.me/submissions/678d1410-4224-49e7-9cf8-748f773a9d15

import Mathlib
import Definitions.Def_GrothendieckLB_E1
import Definitions.Def_GrothendieckLB_Delta

open MeasureTheory ProbabilityTheory

namespace GrothendieckLB

lemma eq43_pfun_le_one (x : ℝ) : Pfun x ≤ 1 := by
  unfold Pfun
  split_ifs
  · exact le_rfl
  · have h := cdf_le_one (gaussianReal 0 1) (Real.sqrt (-2 * Real.log x))
    linarith

lemma eq43_Rfun_le_pi_div_two (x : ℝ) : Rfun x ≤ Real.pi / 2 := by
  have hcGsq : ABPOnline.cG ^ 2 = 2 / Real.pi := by
    rw [ABPOnline.cG, Real.sq_sqrt]
    positivity
  have hcoeff : 1 / ABPOnline.cG ^ 2 = Real.pi / 2 := by
    rw [hcGsq]
    field_simp [Real.pi_ne_zero]
  calc
    Rfun x ≤ (1 / ABPOnline.cG ^ 2) * Pfun x := min_le_right _ _
    _ ≤ (1 / ABPOnline.cG ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left (eq43_pfun_le_one x) (by rw [hcoeff]; positivity)
    _ = Real.pi / 2 := by rw [hcoeff, mul_one]

lemma eq43_one_sub_div_le_log {t : ℝ} (ht : 0 < t) : 1 - 1 / t ≤ Real.log t := by
  have h := Real.log_le_sub_one_of_pos (x := t⁻¹) (by positivity)
  rw [Real.log_inv, ← one_div] at h
  linarith

lemma eq43_delta_lower {x : ℝ} (hx : 0 ≤ x) : 3 * x - 2 ≤ Delta x := by
  have ht : 0 < (1 + x) / 2 := by linarith
  have hlog := eq43_one_sub_div_le_log ht
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1 + x by linarith)
  have hne : 1 + x ≠ 0 := by linarith
  have hcancel : (1 + x) * (1 - 1 / ((1 + x) / 2)) = x - 1 := by
    field_simp [hne] <;> ring
  rw [hcancel] at hmul
  have hb : 0 ≤ (1 - x) + (1 + x) * Real.log ((1 + x) / 2) := by
    linarith
  unfold Delta
  nlinarith

end GrothendieckLB

open GrothendieckLB

theorem solution :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, E1 x ≤ 11 / 6) ∧
    (∀ x ∈ Set.Icc ((1 + 1 / Real.sqrt 3) / 2) (1 : ℝ),
      6 * x ^ 2 - 6 * x + 1 ≤ Delta x ^ 2) := by
  have hs3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs3sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  let s : ℝ := 1 / Real.sqrt 3
  let rm : ℝ := (1 - s) / 2
  let rp : ℝ := (1 + s) / 2
  have hspos : 0 < s := by dsimp [s]; positivity
  have hs_sq : s ^ 2 = 1 / 3 := by
    dsimp [s]
    rw [div_pow, hs3sq, one_pow]
  have hs_lower : 1 / 2 ≤ s := by nlinarith [sq_nonneg s]
  have hs_le_one : s ≤ 1 := by nlinarith [sq_nonneg s]
  have hrm0 : 0 ≤ rm := by dsimp [rm]; linarith
  have hrp0 : 0 ≤ rp := by dsimp [rp]; linarith
  have hrm_sq : 2 * rm ^ 2 = 2 / 3 - s := by
    dsimp [rm]
    nlinarith [hs_sq]
  have hroots_sum : rm + rp = 1 := by dsimp [rm, rp]; ring
  have hroots_mul : rm * rp = 1 / 6 := by
    dsimp [rm, rp]
    nlinarith [hs_sq]
  have hrp_three_quarters : 3 / 4 ≤ rp := by dsimp [rp]; linarith
  have h44 : ∀ x ∈ Set.Icc rp (1 : ℝ), 6 * x ^ 2 - 6 * x + 1 ≤ Delta x ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := hrp0.trans hx.1
    have hdlower : 3 * x - 2 ≤ Delta x := eq43_delta_lower hx0
    have hlin0 : 0 ≤ 3 * x - 2 := by nlinarith [hrp_three_quarters.trans hx.1]
    have hd0 : 0 ≤ Delta x := hlin0.trans hdlower
    have hsquare : (3 * x - 2) ^ 2 ≤ Delta x ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hdlower) (add_nonneg hlin0 hd0)]
    nlinarith [sq_nonneg (1 - x)]
  have h43 : ∀ x ∈ Set.Icc (0 : ℝ) 1, E1 x ≤ 11 / 6 := by
    intro x hx
    by_cases hlow : x ≤ rm
    · have hx_sq : x ^ 2 ≤ rm ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hlow) (add_nonneg hx.1 hrm0)]
      have hE : E1 x ≤ 2 * x ^ 2 + Real.pi / 2 := by
        unfold E1
        have hR := eq43_Rfun_le_pi_div_two x
        have hD := sq_nonneg (DeltaPlus x)
        linarith
      have hnum : 2 * rm ^ 2 + Real.pi / 2 < 11 / 6 := by
        rw [hrm_sq]
        have hpi := Real.pi_lt_d2
        nlinarith
      linarith
    · have hrmx : rm ≤ x := le_of_lt (lt_of_not_ge hlow)
      by_cases hmid : x ≤ rp
      · have hR : Rfun x ≤ 3 * (1 - x) - (1 - x) ^ 2 := min_le_left _ _
        have hE : E1 x ≤ x ^ 2 - x + 2 := by
          unfold E1
          have hD := sq_nonneg (DeltaPlus x)
          nlinarith
        have hprod : (x - rm) * (x - rp) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hrmx) (sub_nonpos.mpr hmid)
        have hfactor : x ^ 2 - x + 1 / 6 = (x - rm) * (x - rp) := by
          nlinarith [hroots_sum, hroots_mul]
        have hquad : x ^ 2 - x + 1 / 6 ≤ 0 := by rw [hfactor]; exact hprod
        linarith
      · have hrpx : rp ≤ x := le_of_lt (lt_of_not_ge hmid)
        have hd44 := h44 x ⟨hrpx, hx.2⟩
        have hx0 : 0 ≤ x := hrp0.trans hrpx
        have hdlower : 3 * x - 2 ≤ Delta x := eq43_delta_lower hx0
        have hlin0 : 0 ≤ 3 * x - 2 := by nlinarith [hrp_three_quarters.trans hrpx]
        have hd0 : 0 ≤ Delta x := hlin0.trans hdlower
        have hDplus : DeltaPlus x = Delta x := max_eq_left hd0
        have hR : Rfun x ≤ 3 * (1 - x) - (1 - x) ^ 2 := min_le_left _ _
        unfold E1
        rw [hDplus]
        nlinarith
  refine ⟨h43, ?_⟩
  simpa [rp, s] using h44
