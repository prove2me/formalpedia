-- Prove2me | solution 1 for NewtonGravitation.shell_angular_integral_value
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:32:59.650993+00:00
-- url     : https://prove2.me/submissions/050b4d7d-0246-4e0c-bf5f-1102d7839578

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

lemma prim_deriv
    (R r t : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hD : 0 < R ^ 2 + r ^ 2 - 2 * R * r * t) :
    HasDerivAt
      (fun u : ℝ =>
        ((R ^ 2 - r ^ 2) / Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * u) -
          Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * u)) / (4 * R ^ 2 * r))
      ((R - r * t) /
        (2 * (Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * t)) ^ 3)) t := by
  set D := R ^ 2 + r ^ 2 - 2 * R * r * t with hDdef
  have hlin : HasDerivAt (fun u : ℝ => R ^ 2 + r ^ 2 - 2 * R * r * u) (-(2 * R * r)) t := by
    have := ((hasDerivAt_id t).const_mul (2 * R * r)).const_sub (R ^ 2 + r ^ 2)
    simpa using this
  have hs : HasDerivAt (fun u : ℝ => Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * u))
      (-(2 * R * r) / (2 * Real.sqrt D)) t := hlin.sqrt hD.ne'
  have hsq : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hF := (((hasDerivAt_const t (R ^ 2 - r ^ 2)).div hs hsq.ne').sub hs).div_const (4 * R ^ 2 * r)
  refine hF.congr_deriv ?_
  have hD2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD.le
  rw [show Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * t) = Real.sqrt D from rfl]
  set s := Real.sqrt D
  rw [hDdef] at hD2
  field_simp
  linear_combination (2 * R * r) * hD2

theorem solution
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hne : r ≠ R) :
    (∫ t in (-1 : ℝ)..1,
        (R - r * t) /
          (2 * (Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * t)) ^ 3)) =
      if r < R then 1 / R ^ 2 else 0 := by
  have hpos : ∀ t ∈ Set.uIcc (-1 : ℝ) 1, 0 < R ^ 2 + r ^ 2 - 2 * R * r * t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have h1 : 0 < (R - r) ^ 2 := by
      have : R - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      positivity
    have : 0 ≤ 2 * R * r * (1 - t) := by
      have : 0 ≤ 1 - t := by linarith [ht.2]
      positivity
    nlinarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => prim_deriv R r t hR hr (hpos t ht))]
  · have e1 : R ^ 2 + r ^ 2 - 2 * R * r * 1 = (R - r) ^ 2 := by ring
    have e2 : R ^ 2 + r ^ 2 - 2 * R * r * (-1) = (R + r) ^ 2 := by ring
    rw [e1, e2, Real.sqrt_sq_eq_abs, Real.sqrt_sq (by linarith)]
    split_ifs with h
    · rw [abs_of_pos (by linarith : 0 < R - r)]
      have : R - r ≠ 0 := by linarith
      field_simp
      ring
    · rw [abs_of_neg (by
        rcases lt_or_gt_of_ne hne with h' | h'
        · exact absurd h' h
        · linarith : R - r < 0)]
      have : R - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have : -(R - r) ≠ 0 := neg_ne_zero.mpr this
      field_simp
      ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · fun_prop
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.pow
      apply ContinuousOn.sqrt
      fun_prop
    · intro t ht
      have := Real.sqrt_pos.mpr (hpos t ht)
      positivity
