-- Prove2me | solution 1 for Kyprianou.Ch01.stableAboveOnePositiveFrequencyKernelScale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:11:24.399337+00:00
-- url     : https://prove2.me/submissions/303b6281-ac06-4f09-9dbd-415f8212cdba

import Mathlib
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem solution
    (alpha xi : ℝ) (ha1 : 1 < alpha) (hxi : 0 < xi) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) - 1 -
        Complex.I * (((xi * r : ℝ) : ℂ))) /
        (((r ^ (alpha + 1) : ℝ) : ℂ)) ∂volume) =
      (((xi ^ alpha : ℝ) : ℂ)) *
        (∫ u in Set.Ioi (0 : ℝ),
          (Complex.exp (Complex.I * (u : ℂ)) - 1 -
            Complex.I * (u : ℂ)) /
            (((u ^ (alpha + 1) : ℝ) : ℂ)) ∂volume) := by
  let F : ℝ → ℂ := fun u =>
    (Complex.exp (Complex.I * (u : ℂ)) - 1 -
      Complex.I * (u : ℂ)) / (((u ^ (alpha + 1) : ℝ) : ℂ))
  have hpoint (r : ℝ) (hr : 0 < r) :
      (Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) - 1 -
        Complex.I * (((xi * r : ℝ) : ℂ))) /
          (((r ^ (alpha + 1) : ℝ) : ℂ)) =
        (((xi ^ (alpha + 1) : ℝ) : ℂ)) * F (xi * r) := by
    have hmul : (xi * r) ^ (alpha + 1) = xi ^ (alpha + 1) * r ^ (alpha + 1) :=
      Real.mul_rpow hxi.le hr.le
    have hxpow : xi ^ (alpha + 1) ≠ 0 :=
      (Real.rpow_pos_of_pos hxi _).ne'
    have hrpow : r ^ (alpha + 1) ≠ 0 :=
      (Real.rpow_pos_of_pos hr _).ne'
    dsimp [F]
    rw [hmul]
    push_cast
    field_simp [hxpow, hrpow]
  have hchange := MeasureTheory.integral_comp_mul_left_Ioi F 0 hxi
  simp only [mul_zero] at hchange
  calc
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) - 1 -
        Complex.I * (((xi * r : ℝ) : ℂ))) /
        (((r ^ (alpha + 1) : ℝ) : ℂ)) ∂volume) =
      ∫ r in Set.Ioi (0 : ℝ),
        (((xi ^ (alpha + 1) : ℝ) : ℂ)) * F (xi * r) ∂volume := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro r hr
          exact hpoint r hr
    _ = (((xi ^ (alpha + 1) : ℝ) : ℂ)) *
        (∫ r in Set.Ioi (0 : ℝ), F (xi * r) ∂volume) := by
          rw [integral_const_mul]
    _ = (((xi ^ (alpha + 1) : ℝ) : ℂ)) *
        (((xi⁻¹ : ℝ) : ℂ) *
          (∫ u in Set.Ioi (0 : ℝ), F u ∂volume)) := by
          rw [hchange]
          simp [RCLike.real_smul_eq_coe_mul]
    _ = (((xi ^ alpha : ℝ) : ℂ)) *
        (∫ u in Set.Ioi (0 : ℝ), F u ∂volume) := by
          have hpow := Real.rpow_add_one hxi.ne' alpha
          rw [hpow]
          push_cast
          field_simp [hxi.ne']
    _ = _ := rfl
