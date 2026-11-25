-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_exp_grid_linearization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:07:15.874865+00:00
-- url     : https://prove2.me/submissions/032434d9-2e37-4ea7-b522-b7730979aa1f

import Mathlib.Analysis.Complex.Exponential
set_option autoImplicit false

/-- First-order expansion of the exponential integrating factor on
finite grids with small increments and bounded total variation. -/
theorem solution
    (Z d : Nat → Real) (N : Nat) (eta C : Real)
    (hEta : 0 ≤ eta) (hEta1 : eta ≤ 1)
    (hZ : ∀ i, |Z i| ≤ 1)
    (hSmall : ∀ i < N, |d i| ≤ eta)
    (hVar : (∑ i ∈ Finset.range N, |d i|) ≤ C) :
    |(∑ i ∈ Finset.range N, Z i * (1 - Real.exp (-d i))) -
      (∑ i ∈ Finset.range N, Z i * d i)| ≤ eta * C := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range N, |Z i * (1 - Real.exp (-d i)) - Z i * d i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, eta * |d i| := by
      apply Finset.sum_le_sum
      intro i hi
      have hs := hSmall i (Finset.mem_range.mp hi)
      have hTaylor : |Real.exp (-d i) - 1 - (-d i)| ≤ (-d i)^2 :=
        Real.abs_exp_sub_one_sub_id_le (by rw [abs_neg]; exact hs.trans hEta1)
      have hErr : |1 - Real.exp (-d i) - d i| ≤ (d i)^2 := by
        rw [show 1 - Real.exp (-d i) - d i =
          -(Real.exp (-d i) - 1 - (-d i)) by ring, abs_neg]
        simpa only [neg_sq] using hTaylor
      rw [← mul_sub, abs_mul]
      calc
        _ ≤ 1 * |1 - Real.exp (-d i) - d i| :=
          mul_le_mul_of_nonneg_right (hZ i) (abs_nonneg _)
        _ ≤ (d i)^2 := by simpa using hErr
        _ = |d i| * |d i| := by rw [← sq_abs]; ring
        _ ≤ eta * |d i| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    _ = eta * (∑ i ∈ Finset.range N, |d i|) := by rw [Finset.mul_sum]
    _ ≤ eta * C := mul_le_mul_of_nonneg_left hVar hEta
