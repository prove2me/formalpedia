-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.ArcsineIntegral.integral_inv_add_mul_cos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/3f6870b1-4bb7-4ef8-8c70-23f2848b2c7f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory Real Set
open scoped Interval
open MetricCodes.Spherical.HigherHierarchy.ArcsineIntegral
namespace MetricCodes.Spherical.HigherHierarchy.ArcsineIntegral
theorem _root_.solution (a b : ℝ) (h : |b| < a) :
    (∫ θ in (0 : ℝ)..Real.pi, (a + b * Real.cos θ)⁻¹) =
      Real.pi / Real.sqrt (a ^ 2 - b ^ 2) := by
  have hab : -a < b ∧ b < a := abs_lt.mp h
  have hplus : 0 < a + b := by linarith [hab.1]
  have hminus : 0 < a - b := by linarith [hab.2]
  have hdisc : 0 < a ^ 2 - b ^ 2 := by
    nlinarith [mul_pos hplus hminus]
  let c : ℝ := Real.sqrt (a ^ 2 - b ^ 2)
  have hc : 0 < c := Real.sqrt_pos.2 hdisc
  have hden (θ : ℝ) : 0 < a + b * Real.cos θ := by
    have hbound : |b * Real.cos θ| ≤ |b| := by
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ)
        (abs_nonneg b)
    linarith [neg_le_of_abs_le hbound]
  let q : ℝ → ℝ := fun θ =>
    (a * Real.cos θ + b) / (a + b * Real.cos θ)
  let F : ℝ → ℝ := fun θ => -Real.arcsin (q θ) / c
  have hqcont : Continuous q := by
    exact ((continuous_const.mul Real.continuous_cos).add continuous_const).div
      (continuous_const.add (continuous_const.mul Real.continuous_cos))
      (fun θ => (hden θ).ne')
  have hFcont : Continuous F :=
    (Real.continuous_arcsin.comp hqcont).neg.div_const c
  have hintegrable :
      IntervalIntegrable (fun θ : ℝ => (a + b * Real.cos θ)⁻¹)
        volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.add
      (continuous_const.mul Real.continuous_cos)).inv₀
        (fun θ => (hden θ).ne')
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi,
      HasDerivAt F ((a + b * Real.cos θ)⁻¹) θ := by
    intro θ hθ
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have hqidentity :
        1 - (q θ) ^ 2 =
          (a ^ 2 - b ^ 2) * (Real.sin θ) ^ 2 /
            (a + b * Real.cos θ) ^ 2 := by
      have htrig : (Real.sin θ) ^ 2 = 1 - (Real.cos θ) ^ 2 := by
        linarith [Real.sin_sq_add_cos_sq θ]
      have hd2 : (a + b * Real.cos θ) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (hden θ).ne'
      rw [htrig]
      dsimp [q]
      rw [div_pow]
      calc
        1 - (a * Real.cos θ + b) ^ 2 / (a + b * Real.cos θ) ^ 2 =
            ((a + b * Real.cos θ) ^ 2 -
              (a * Real.cos θ + b) ^ 2) /
              (a + b * Real.cos θ) ^ 2 := by
          rw [sub_div, div_self hd2]
        _ = (a ^ 2 - b ^ 2) * (1 - Real.cos θ ^ 2) /
              (a + b * Real.cos θ) ^ 2 := by
          congr 1
          ring
    have hqsmall : (q θ) ^ 2 < 1 := by
      have hpos : 0 <
          (a ^ 2 - b ^ 2) * (Real.sin θ) ^ 2 /
            (a + b * Real.cos θ) ^ 2 :=
        div_pos (mul_pos hdisc (sq_pos_of_pos hsin))
          (sq_pos_of_pos (hden θ))
      linarith [hqidentity]
    have hqlower : -1 < q θ := by nlinarith [sq_nonneg (q θ + 1)]
    have hqupper : q θ < 1 := by nlinarith [sq_nonneg (q θ - 1)]
    have hroot :
        Real.sqrt (1 - (q θ) ^ 2) =
          c * Real.sin θ / (a + b * Real.cos θ) := by
      rw [hqidentity, Real.sqrt_div (mul_nonneg hdisc.le (sq_nonneg _)),
        Real.sqrt_mul hdisc.le, Real.sqrt_sq hsin.le,
        Real.sqrt_sq (hden θ).le]
    have hqderiv :
        HasDerivAt q
          (-(a ^ 2 - b ^ 2) * Real.sin θ /
            (a + b * Real.cos θ) ^ 2) θ := by
      dsimp [q]
      refine ((((Real.hasDerivAt_cos θ).const_mul a).add_const b).div
        (((Real.hasDerivAt_cos θ).const_mul b).const_add a)
        (hden θ).ne').congr_deriv ?_
      ring
    have harcsin :=
      (Real.hasDerivAt_arcsin (ne_of_gt hqlower) (ne_of_lt hqupper)).comp
        θ hqderiv
    have hF :
        HasDerivAt F
          (-(1 / Real.sqrt (1 - (q θ) ^ 2) *
            (-(a ^ 2 - b ^ 2) * Real.sin θ /
              (a + b * Real.cos θ) ^ 2)) / c) θ := by
      simpa [F, Function.comp_def] using harcsin.neg.div_const c
    refine hF.congr_deriv ?_
    rw [hroot]
    have hcsq : c ^ 2 = a ^ 2 - b ^ 2 :=
      Real.sq_sqrt hdisc.le
    field_simp [hc.ne', (hden θ).ne', hsin.ne']
    nlinarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    Real.pi_pos.le hFcont.continuousOn hderiv hintegrable]
  dsimp [F, q]
  rw [Real.cos_pi, Real.cos_zero]
  have hqpi : (a * (-1) + b) / (a + b * (-1)) = -1 := by
    have hne : a + b * (-1) ≠ 0 := by
      simpa [sub_eq_add_neg] using hminus.ne'
    apply (div_eq_iff hne).2
    ring
  have hqzero : (a * 1 + b) / (a + b * 1) = 1 := by
    have hne : a + b * 1 ≠ 0 := by simpa using hplus.ne'
    apply (div_eq_iff hne).2
    ring
  rw [hqpi, hqzero, Real.arcsin_neg_one, Real.arcsin_one]
  dsimp [c]
  ring
end MetricCodes.Spherical.HigherHierarchy.ArcsineIntegral
