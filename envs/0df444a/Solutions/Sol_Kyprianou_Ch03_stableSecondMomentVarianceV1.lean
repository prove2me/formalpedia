-- Prove2me | solution 1 for Kyprianou.Ch03.stableSecondMomentVarianceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:57:50.443138+00:00
-- url     : https://prove2.me/submissions/b7b3201d-7dea-45a6-b7af-080f70ce2d04

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Omega → ℝ) (hi : Integrable Z P) (hi2 : Integrable (fun w => Z w ^ 2) P) :
    (∫ w, Z w ∂P)^2 ≤ ∫ w, Z w^2 ∂P ∧
      ((∫ w, Z w ∂P) = 1 → (∫ w, Z w^2 ∂P) = 1 → Z =ᵐ[P] 1) := by
  let a : ℝ := ∫ w, Z w ∂P
  let r : ℝ := ∫ w, Z w ^ 2 ∂P
  have hv (m : ℝ) : (∫ w, (Z w - m)^2 ∂P) = r - 2*m*a + m^2 := by
    have h : (fun w => (Z w - m)^2) = fun w => Z w ^ 2 - (2*m) * Z w + m^2 := by
      funext w; ring
    have hmul : Integrable (fun w => (2*m) * Z w) P := hi.const_mul _
    have hsub : Integrable (fun w => Z w^2 - (2*m) * Z w) P := hi2.sub hmul
    rw [h, integral_add hsub (integrable_const (m^2)),
      integral_sub hi2 hmul, integral_const_mul]
    simp [a, r, Measure.real]
  refine ⟨?_, ?_⟩
  · have hvn : 0 ≤ (∫ w, (Z w - a)^2 ∂P) := integral_nonneg (fun w => sq_nonneg _)
    rw [hv] at hvn
    change a^2 ≤ r
    nlinarith
  · intro ha hr
    have hiV : Integrable (fun w => (Z w - 1)^2) P := by
      have hmul : Integrable (fun w => 2 * Z w) P := hi.const_mul 2
      have hsub : Integrable (fun w => Z w^2 - 2 * Z w) P := hi2.sub hmul
      have hadd : Integrable (fun w => Z w^2 - 2 * Z w + 1) P :=
        hsub.add (integrable_const (1:ℝ))
      apply hadd.congr
      filter_upwards with w
      ring
    have hV : (∫ w, (Z w - 1)^2 ∂P) = 0 := by
      rw [hv]; change a = 1 at ha; change r = 1 at hr
      rw [ha, hr]; norm_num
    have he := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun w => sq_nonneg (Z w - 1)) hiV).mp hV
    filter_upwards [he] with w hw
    change (Z w - 1)^2 = 0 at hw
    change Z w = 1
    nlinarith
