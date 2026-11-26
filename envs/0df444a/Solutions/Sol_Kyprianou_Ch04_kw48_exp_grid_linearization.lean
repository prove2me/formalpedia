-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_exp_grid_linearization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:38:09.775557+00:00
-- url     : https://prove2.me/submissions/48c7b3f6-1644-4c30-8e5d-a3ae4c4ebf7f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Ring.Basic
import Theorems.Thm_Kyprianou_Ch04_kw48_exp_remainder
set_option autoImplicit false

/-- Uniform quadratic control of the complex exponential grid error. -/
theorem solution (Z d : Nat → Complex) (N : Nat) (eta C : Real)
    (hEta : 0 ≤ eta) (hEta1 : eta ≤ 1)
    (hZ : ∀ i, ‖Z i‖ ≤ 1)
    (hSmall : ∀ i < N, ‖d i‖ ≤ eta)
    (hVar : (∑ i ∈ Finset.range N, ‖d i‖) ≤ C) :
    ‖(∑ i ∈ Finset.range N, Z i * (1-Complex.exp (-d i))) -
      (∑ i ∈ Finset.range N, Z i * d i)‖ ≤ eta*C := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range N, ‖Z i*(1-Complex.exp (-d i))-Z i*d i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range N, eta*‖d i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      have hs := hSmall i (Finset.mem_range.mp hi)
      have hErr := Kyprianou.Ch04.kw48_exp_remainder (d i) (hs.trans hEta1)
      rw [← mul_sub,norm_mul]
      calc
        _ ≤ 1*‖1-Complex.exp (-d i)-d i‖ :=
          mul_le_mul_of_nonneg_right (hZ i) (norm_nonneg _)
        _ ≤ ‖d i‖^2 := by simpa using hErr
        _ ≤ eta*‖d i‖ := by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ = eta*(∑ i ∈ Finset.range N, ‖d i‖) := by rw [Finset.mul_sum]
    _ ≤ eta*C := mul_le_mul_of_nonneg_left hVar hEta
