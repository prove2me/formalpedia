-- Prove2me | solution 1 for Kyprianou.Ch03.stableLogLaplaceCoefficientStrictSignV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:39:11.95387+00:00
-- url     : https://prove2.me/submissions/56023da1-529e-4d0b-8a8e-93417986ae74

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_stableSecondMomentVarianceV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] (Y : Omega → ℝ)
    (alpha : ℝ) (ha : 0 < alpha) (hne : ¬ Y =ᵐ[P] 0)
    (hi : ∀ theta : ℝ, 0 ≤ theta → Integrable (fun w => Real.exp (-theta * Y w)) P)
    (hh : ∀ theta : ℝ, 0 ≤ theta →
      Real.log (∫ w, Real.exp (-theta * Y w) ∂P) =
        Real.log (∫ w, Real.exp (-Y w) ∂P) * theta ^ alpha) :
    (alpha < 1 → Real.log (∫ w, Real.exp (-Y w) ∂P) < 0) ∧
    (1 < alpha → 0 < Real.log (∫ w, Real.exp (-Y w) ∂P)) := by
  let Z : Omega → ℝ := fun w => Real.exp (-Y w)
  let a : ℝ := ∫ w, Z w ∂P
  let r : ℝ := ∫ w, Z w ^ 2 ∂P
  have hiZ : Integrable Z P := by simpa [Z] using hi 1 (by norm_num)
  have hiZ2 : Integrable (fun w => Z w ^ 2) P := by
    convert hi 2 (by norm_num) using 1
    funext w
    dsimp [Z]
    rw [← Real.exp_nat_mul]
    push_cast; ring
  have ha0 : 0 < a := by
    apply (integral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun w => (Real.exp_pos _).le) hiZ).mpr
    have hsupport : Function.support Z = Set.univ := by
      ext w; simp [Z, Function.mem_support, Real.exp_ne_zero]
    rw [hsupport, measure_univ]; norm_num
  have hvar := Kyprianou.Ch03.stableSecondMomentVarianceV1 P Z hiZ hiZ2
  have hra : a^2 ≤ r := hvar.1
  have hr0 : 0 < r := (sq_pos_of_pos ha0).trans_le hra
  have h2 : Real.log r = Real.log a * (2 : ℝ)^alpha := by
    have he : (fun w => Z w ^ 2) = fun w => Real.exp (-(2:ℝ) * Y w) := by
      funext w
      dsimp [Z]
      rw [← Real.exp_nat_mul]; push_cast; ring
    simpa [r, he, a, Z, neg_one_mul] using hh 2 (by norm_num)
  have hlog := Real.log_le_log (sq_pos_of_pos ha0) hra
  rw [Real.log_pow, h2] at hlog
  have hneC : Real.log a ≠ 0 := by
    intro hzero
    have ha1 : a = 1 := by simpa [hzero] using (Real.exp_log ha0).symm
    have hr1 : r = 1 := by simpa [h2, hzero] using (Real.exp_log hr0).symm
    have he := hvar.2 ha1 hr1
    apply hne
    filter_upwards [he] with w hw
    have hz : Z w = 1 := hw
    have hz' : Real.exp (-Y w) = Real.exp 0 := by simpa [Z] using hz
    have hy := Real.exp_injective hz'
    change Y w = 0
    linarith
  constructor
  · intro hlt
    have hpow : (2 : ℝ)^alpha < 2 := by
      calc
        _ < (2 : ℝ)^(1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
        _ = 2 := Real.rpow_one _
    change Real.log a < 0
    by_contra! h
    have hpos := lt_of_le_of_ne h hneC.symm
    push_cast at hlog
    nlinarith [mul_pos hpos (sub_pos.mpr hpow)]
  · intro hgt
    have hpow : (2 : ℝ) < (2 : ℝ)^alpha := by
      calc
        (2 : ℝ) = (2 : ℝ)^(1 : ℝ) := (Real.rpow_one _).symm
        _ < _ := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hgt
    change 0 < Real.log a
    by_contra! h
    have hneg := lt_of_le_of_ne h hneC
    push_cast at hlog
    nlinarith [mul_neg_of_neg_of_pos hneg (sub_pos.mpr hpow)]
