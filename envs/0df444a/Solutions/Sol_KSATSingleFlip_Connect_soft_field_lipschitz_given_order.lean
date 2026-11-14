-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_lipschitz_given_order
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:31:44.467446+00:00
-- url     : https://prove2.me/submissions/4909db9e-c7be-4fe5-8bc5-26ec12d1fd1f

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_order_mass_potential_gap
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_recursion_mass
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_finite_intensity
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

private theorem exp_gap (x y : ℝ) (hxy : x ≤ y) : Real.exp y-Real.exp x ≤ Real.exp y*(y-x) := by
  have h := Real.add_one_le_exp (x-y)
  have hm := mul_le_mul_of_nonneg_right h (le_of_lt (Real.exp_pos y))
  have he : Real.exp (x-y)*Real.exp y = Real.exp x := by rw [← Real.exp_add]; congr 1; ring
  rw [he] at hm
  nlinarith

theorem solution (ν' ν : Measure ℝ) [IsFiniteMeasure ν'] [IsFiniteMeasure ν] (β : ℝ) (hβ : 0 ≤ β)
    (hu' : (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν') ≠ ∞)
    (hu : (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν) ≠ ∞)
    (hord : softFieldLE ν' ν) (hord' : softFieldLE (Rbeta β ν') (Rbeta β ν)) :
    0 ≤ hPot (Rbeta β ν)-hPot (Rbeta β ν') ∧
      hPot (Rbeta β ν)-hPot (Rbeta β ν') ≤ β*Real.exp (hPot ν)*(hPot ν-hPot ν') := by
  have hrec' := soft_field_recursion_mass ν' β hβ (soft_field_finite_intensity ν' hu')
  have hrec := soft_field_recursion_mass ν β hβ (soft_field_finite_intensity ν hu)
  letI : IsFiniteMeasure (Rbeta β ν') := ⟨by
    unfold Rbeta
    rw [Measure.smul_apply, smul_eq_mul, hrec'.1, mul_one]
    exact ENNReal.ofReal_lt_top⟩
  letI : IsFiniteMeasure (Rbeta β ν) := ⟨by
    unfold Rbeta
    rw [Measure.smul_apply, smul_eq_mul, hrec.1, mul_one]
    exact ENNReal.ofReal_lt_top⟩
  have hold := soft_field_order_mass_potential_gap ν' ν hord
  have hnew := soft_field_order_mass_potential_gap (Rbeta β ν') (Rbeta β ν) hord'
  rw [hrec.2,hrec'.2] at hnew
  have hcmp := exp_gap (hPot ν') (hPot ν) (by linarith [hold.1])
  have hcmp' := mul_le_mul_of_nonneg_left hcmp hβ
  constructor
  · exact hnew.1
  · nlinarith
