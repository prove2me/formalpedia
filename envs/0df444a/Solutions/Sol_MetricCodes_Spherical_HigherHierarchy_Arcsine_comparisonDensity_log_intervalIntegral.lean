-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Arcsine.comparisonDensity_log_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/54b15c7b-58bd-44e9-92f6-495f0c058830

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Interval
open MetricCodes.Spherical.HigherHierarchy.Arcsine
namespace MetricCodes.Spherical.HigherHierarchy.Arcsine
theorem _root_.solution :
    (∫ t in (0 : ℝ)..(1 / 4 : ℝ),
      Real.log t / Real.sqrt (1 / 4 - t)) = -2 := by
  have hsubst := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := fun u : ℝ => (1 - u ^ 2) / 4)
    (f' := fun u : ℝ => -u / 2)
    (g := fun t : ℝ => Real.log t / Real.sqrt (1 / 4 - t))
    (by fun_prop)
    (by
      intro u hu
      convert (((hasDerivAt_id u).pow 2).const_sub 1).div_const 4 using 1 <;>
        try rfl
      norm_num [id]
      ring)
    (by
      intro u hu
      norm_num at hu
      linarith [hu.1])
  norm_num at hsubst
  have hleft :
      (∫ u in (0 : ℝ)..1,
        (-u / 2) *
          (Real.log ((1 - u ^ 2) / 4) /
            Real.sqrt (1 / 4 - (1 - u ^ 2) / 4))) =
        ∫ u in (0 : ℝ)..1, -Real.log ((1 - u ^ 2) / 4) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    change (-u / 2) *
      (Real.log ((1 - u ^ 2) / 4) /
        Real.sqrt (1 / 4 - (1 - u ^ 2) / 4)) =
      -Real.log ((1 - u ^ 2) / 4)
    have hu0 : 0 < u := hu.1
    have hsqrt : Real.sqrt (u ^ 2 / 4) = u / 2 := by
      rw [Real.sqrt_div' (u ^ 2) (by norm_num : (0 : ℝ) ≤ 4),
        Real.sqrt_sq hu0.le]
      norm_num
    have hrad : (1 / 4 : ℝ) - (1 - u ^ 2) / 4 = u ^ 2 / 4 := by ring
    rw [hrad, hsqrt]
    field_simp
  rw [hleft] at hsubst
  have hright :
      (∫ t in (1 / 4 : ℝ)..0,
        Real.log t / Real.sqrt (1 / 4 - t)) =
        -(∫ t in (0 : ℝ)..(1 / 4 : ℝ),
          Real.log t / Real.sqrt (1 / 4 - t)) :=
    intervalIntegral.integral_symm _ _
  rw [hright] at hsubst
  have hsplit :
      (∫ u in (0 : ℝ)..1, Real.log ((1 - u ^ 2) / 4)) = -2 := by
    have hminus :
        IntervalIntegrable (fun u : ℝ => Real.log (1 - u)) volume 0 1 := by
      simpa using
        ((intervalIntegral.intervalIntegrable_log'
          (a := (0 : ℝ)) (b := 1)).comp_sub_left 1).symm
    have hplus :
        IntervalIntegrable (fun u : ℝ => Real.log (1 + u)) volume 0 1 := by
      convert
        (intervalIntegral.intervalIntegrable_log'
          (a := (1 : ℝ)) (b := 2)).comp_add_left 1
        using 1 <;> norm_num
    calc
      (∫ u in (0 : ℝ)..1, Real.log ((1 - u ^ 2) / 4)) =
          ∫ u in (0 : ℝ)..1,
            (Real.log (1 - u) + Real.log (1 + u)) - Real.log 4 := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro u hu
        change Real.log ((1 - u ^ 2) / 4) =
          Real.log (1 - u) + Real.log (1 + u) - Real.log 4
        have hleft : 0 < 1 - u := sub_pos.mpr hu.2
        have hright : 0 < 1 + u := by linarith [hu.1]
        rw [show (1 - u ^ 2) / 4 = ((1 - u) * (1 + u)) / 4 by ring,
          Real.log_div (mul_pos hleft hright).ne' (by norm_num),
          Real.log_mul hleft.ne' hright.ne']
      _ =
          ((∫ u in (0 : ℝ)..1, Real.log (1 - u)) +
            (∫ u in (0 : ℝ)..1, Real.log (1 + u))) -
              (∫ _u in (0 : ℝ)..1, Real.log 4) := by
        rw [intervalIntegral.integral_sub (hminus.add hplus)
          (intervalIntegrable_const :
            IntervalIntegrable (fun _ : ℝ => Real.log 4) volume 0 1),
          intervalIntegral.integral_add hminus hplus]
      _ = -2 := by
        rw [intervalIntegral.integral_comp_sub_left Real.log 1,
          intervalIntegral.integral_comp_add_left Real.log 1,
          integral_log, integral_log]
        norm_num
        rw [show (4 : ℝ) = 2 * 2 by norm_num,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num)]
        ring
  rw [intervalIntegral.integral_neg, hsplit] at hsubst
  linarith
end MetricCodes.Spherical.HigherHierarchy.Arcsine
