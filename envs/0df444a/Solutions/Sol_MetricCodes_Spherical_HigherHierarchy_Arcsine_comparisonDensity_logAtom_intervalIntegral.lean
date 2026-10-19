-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Arcsine.comparisonDensity_logAtom_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/a2967809-8ab7-4511-9b94-4eb69d3e162a

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
theorem _root_.solution
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in (0 : ℝ)..(1 / 4 : ℝ),
      Real.log ((t + a * (1 + a)) / t) /
        Real.sqrt (1 / 4 - t)) =
      2 * ((1 + a) * Real.log (1 + a) - a * Real.log a) := by
  by_cases ha0 : a = 0
  · subst a
    have hzero :
        (∫ t in (0 : ℝ)..(1 / 4 : ℝ),
          Real.log ((t + 0 * (1 + 0)) / t) /
            Real.sqrt (1 / 4 - t)) = 0 := by
      calc
        (∫ t in (0 : ℝ)..(1 / 4 : ℝ),
          Real.log ((t + 0 * (1 + 0)) / t) /
            Real.sqrt (1 / 4 - t)) =
            ∫ _t in (0 : ℝ)..(1 / 4 : ℝ), 0 := by
          apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
          intro t ht
          change Real.log ((t + 0 * (1 + 0)) / t) /
            Real.sqrt (1 / 4 - t) = 0
          simp [ht.1.ne']
        _ = 0 := by simp
    simp at hzero ⊢
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  let b : ℝ := 2 * a + 1
  have hb : 1 < b := by dsimp [b]; linarith
  have hsubst := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := fun u : ℝ => (1 - u ^ 2) / 4)
    (f' := fun u : ℝ => -u / 2)
    (g := fun t : ℝ =>
      Real.log ((t + a * (1 + a)) / t) / Real.sqrt (1 / 4 - t))
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
          (Real.log (((1 - u ^ 2) / 4 + a * (1 + a)) /
            ((1 - u ^ 2) / 4)) /
            Real.sqrt (1 / 4 - (1 - u ^ 2) / 4))) =
        ∫ u in (0 : ℝ)..1,
          -Real.log (((1 - u ^ 2) / 4 + a * (1 + a)) /
            ((1 - u ^ 2) / 4)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    change (-u / 2) *
      (Real.log (((1 - u ^ 2) / 4 + a * (1 + a)) /
        ((1 - u ^ 2) / 4)) /
        Real.sqrt (1 / 4 - (1 - u ^ 2) / 4)) =
      -Real.log (((1 - u ^ 2) / 4 + a * (1 + a)) /
        ((1 - u ^ 2) / 4))
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
        Real.log ((t + a * (1 + a)) / t) /
          Real.sqrt (1 / 4 - t)) =
        -(∫ t in (0 : ℝ)..(1 / 4 : ℝ),
          Real.log ((t + a * (1 + a)) / t) /
            Real.sqrt (1 / 4 - t)) :=
    intervalIntegral.integral_symm _ _
  rw [hright] at hsubst
  have hsplit :
      (∫ u in (0 : ℝ)..1,
        Real.log (((1 - u ^ 2) / 4 + a * (1 + a)) /
          ((1 - u ^ 2) / 4))) =
        2 * ((1 + a) * Real.log (1 + a) - a * Real.log a) := by
    have hminus1 :
        IntervalIntegrable (fun u : ℝ => Real.log (1 - u)) volume 0 1 := by
      simpa using
        ((intervalIntegral.intervalIntegrable_log'
          (a := (0 : ℝ)) (b := 1)).comp_sub_left 1).symm
    have hplus1 :
        IntervalIntegrable (fun u : ℝ => Real.log (1 + u)) volume 0 1 := by
      convert
        (intervalIntegral.intervalIntegrable_log'
          (a := (1 : ℝ)) (b := 2)).comp_add_left 1
        using 1 <;> norm_num
    have hminusB :
        IntervalIntegrable (fun u : ℝ => Real.log (b - u)) volume 0 1 := by
      refine (ContinuousOn.log
        (continuous_const.sub continuous_id).continuousOn ?_).intervalIntegrable
      intro u hu
      have hu' : u ≤ 1 := by simpa using hu.2
      exact (sub_pos.mpr (lt_of_le_of_lt hu' hb)).ne'
    have hplusB :
        IntervalIntegrable (fun u : ℝ => Real.log (b + u)) volume 0 1 := by
      refine (ContinuousOn.log
        (continuous_const.add continuous_id).continuousOn ?_).intervalIntegrable
      intro u hu
      have hu' : 0 ≤ u := by simpa using hu.1
      have hb' : 0 < b := lt_trans (by norm_num) hb
      exact (add_pos_of_pos_of_nonneg hb' hu').ne'
    calc
      (∫ u in (0 : ℝ)..1,
        Real.log (((1 - u ^ 2) / 4 + a * (1 + a)) /
          ((1 - u ^ 2) / 4))) =
          ∫ u in (0 : ℝ)..1,
            (Real.log (b - u) + Real.log (b + u)) -
              (Real.log (1 - u) + Real.log (1 + u)) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro u hu
        change Real.log (((1 - u ^ 2) / 4 + a * (1 + a)) /
          ((1 - u ^ 2) / 4)) =
          (Real.log (b - u) + Real.log (b + u)) -
            (Real.log (1 - u) + Real.log (1 + u))
        have hminus : 0 < 1 - u := sub_pos.mpr hu.2
        have hplus : 0 < 1 + u := by linarith [hu.1]
        have hbminus : 0 < b - u := by linarith [hb, hu.2]
        have hbplus : 0 < b + u := by linarith [hb, hu.1]
        have hratio :
            ((1 - u ^ 2) / 4 + a * (1 + a)) / ((1 - u ^ 2) / 4) =
              ((b - u) * (b + u)) / ((1 - u) * (1 + u)) := by
          dsimp [b]
          have hden : 1 - u ^ 2 ≠ 0 := by
            nlinarith [mul_pos hminus hplus]
          field_simp
          ring
        rw [hratio,
          Real.log_div (mul_pos hbminus hbplus).ne'
            (mul_pos hminus hplus).ne',
          Real.log_mul hbminus.ne' hbplus.ne',
          Real.log_mul hminus.ne' hplus.ne']
      _ =
          (((∫ u in (0 : ℝ)..1, Real.log (b - u)) +
            (∫ u in (0 : ℝ)..1, Real.log (b + u))) -
              ((∫ u in (0 : ℝ)..1, Real.log (1 - u)) +
                (∫ u in (0 : ℝ)..1, Real.log (1 + u)))) := by
        rw [intervalIntegral.integral_sub (hminusB.add hplusB)
          (hminus1.add hplus1),
          intervalIntegral.integral_add hminusB hplusB,
          intervalIntegral.integral_add hminus1 hplus1]
      _ = 2 * ((1 + a) * Real.log (1 + a) - a * Real.log a) := by
        rw [intervalIntegral.integral_comp_sub_left Real.log b,
          intervalIntegral.integral_comp_add_left Real.log b,
          intervalIntegral.integral_comp_sub_left Real.log 1,
          intervalIntegral.integral_comp_add_left Real.log 1,
          integral_log, integral_log, integral_log, integral_log]
        norm_num
        have hbminus : b - 1 = 2 * a := by dsimp [b]; ring
        have hbplus : b + 1 = 2 * (1 + a) := by dsimp [b]; ring
        rw [hbminus, hbplus,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
            (by linarith [ha'] : 1 + a ≠ 0)]
        ring
  rw [intervalIntegral.integral_neg, hsplit] at hsubst
  linarith
end MetricCodes.Spherical.HigherHierarchy.Arcsine
