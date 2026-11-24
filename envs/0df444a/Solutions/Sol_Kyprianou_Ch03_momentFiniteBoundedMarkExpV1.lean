-- Prove2me | solution 1 for Kyprianou.Ch03.momentFiniteBoundedMarkExpV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:45:18.335229+00:00
-- url     : https://prove2.me/submissions/3eb5bc67-93fa-4788-b556-477776546a97

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (nu : Measure Real) [IsFiniteMeasure nu]
    (hnu : ∀ᵐ x ∂nu, |x| < 1) (b : Real) :
    Integrable (fun x : Real => Real.exp (b * x)) nu := by
  apply (integrable_const (Real.exp |b|)).mono (by fun_prop)
  filter_upwards [hnu] with x hx
  have h : |b*x| ≤ |b| := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx.le (abs_nonneg b)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
  exact (le_abs_self _).trans h
