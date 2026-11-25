-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_grid_gain_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:04:32.440723+00:00
-- url     : https://prove2.me/submissions/0859f50d-d533-4566-911b-88aef9eda24a

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_Kyprianou_Ch04_kw47_discrete_product_summation
set_option autoImplicit false

/-- Grid product gains are uniformly dominated by endpoint suprema
and deterministic variation of the multiplier. -/
theorem solution
    (E H : Nat → Real) (n : Nat) (S C : Real)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hE : ∀ i, |E i| ≤ S)
    (hH : ∀ i, |H i| ≤ C)
    (hVarH : (∑ i ∈ Finset.range n,
      |H (i+1) - H i|) ≤ 2*C) :
    |∑ i ∈ Finset.range n, H i * (E (i+1) - E i)|
      ≤ 4 * S * C := by
  have hTerm (i : Nat) :
      |E (i+1) * (H (i+1) - H i)|
        ≤ S * |H (i+1) - H i| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hE (i+1)) (abs_nonneg _)
  have hSum :
      |∑ i ∈ Finset.range n, E (i+1) * (H (i+1)-H i)|
        ≤ 2*S*C := by
    calc
      |∑ i ∈ Finset.range n, E (i+1) * (H (i+1)-H i)|
        ≤ ∑ i ∈ Finset.range n, |E (i+1) * (H (i+1)-H i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n, S * |H (i+1)-H i| :=
          Finset.sum_le_sum (fun i _ => hTerm i)
      _ = S * (∑ i ∈ Finset.range n, |H (i+1)-H i|) := by
          rw [Finset.mul_sum]
      _ ≤ S*(2*C) := mul_le_mul_of_nonneg_left hVarH hS
      _ = 2*S*C := by ring
  have hEndpoint (i : Nat) : |E i * H i| ≤ S*C := by
    rw [abs_mul]
    exact mul_le_mul (hE i) (hH i) (abs_nonneg _) hS
  rw [Kyprianou.Ch04.kw47_discrete_product_summation]
  have hTri :
      |E n * H n - E 0 * H 0 -
        ∑ i ∈ Finset.range n, E (i+1) * (H (i+1)-H i)|
      ≤ |E n * H n| + |E 0 * H 0| +
          |∑ i ∈ Finset.range n, E (i+1) * (H (i+1)-H i)| := by
    calc
      |E n * H n - E 0 * H 0 -
        ∑ i ∈ Finset.range n, E (i+1) * (H (i+1)-H i)|
        ≤ |E n * H n - E 0 * H 0| +
            |∑ i ∈ Finset.range n, E (i+1) * (H (i+1)-H i)| :=
          (by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le (E n * H n - E 0 * H 0) (0 : Real)
                (∑ i ∈ Finset.range n,
                  E (i+1) * (H (i+1)-H i))))
      _ ≤ |E n * H n| + |E 0 * H 0| +
            |∑ i ∈ Finset.range n, E (i+1) * (H (i+1)-H i)| := by
          gcongr
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (E n * H n) (0 : Real) (E 0 * H 0))
  nlinarith [hTri, hEndpoint n, hEndpoint 0, hSum]
