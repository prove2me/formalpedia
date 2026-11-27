-- Prove2me | solution 1 for Kyprianou.Ch04.affineGridLedgerVariationBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:46:12.993539+00:00
-- url     : https://prove2.me/submissions/0053750e-f7a2-45cf-9947-c24662bc903e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_positive_monotone_grid_variation
open MeasureTheory Set
open scoped NNReal Classical
set_option autoImplicit false

/-- Summing the absolute increments of an affine path ledger is bounded
by the sum of the absolute variation budgets of its constituents. -/
theorem solution (S : Finset NNReal) (a : NNReal → ℝ) (b T : ℝ)
    (n : ℕ) (v y : ℕ → ℝ) (J : NNReal → ℕ → ℝ)
    (he : ∀ k, y (k+1)-y k = b*(v (k+1)-v k) +
      ∑ r ∈ S,a r*(J r (k+1)-J r k))
    (hV : (∑ k ∈ Finset.range n, |v (k+1)-v k|) ≤ T)
    (hJ' : ∀ r, (∑ k ∈ Finset.range n, |J r (k+1)-J r k|) ≤ 1) :
    (∑ k ∈ Finset.range n, |y (k+1)-y k|) ≤ |b| * T+∑ r ∈ S,|a r| := by
  calc
      _ ≤ ∑ k ∈ Finset.range n, (|b| * |v (k+1)-v k| +
          ∑ r ∈ S, |a r| * |J r (k+1)-J r k|) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [he k]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
        apply add_le_add_right
        simpa only [abs_mul] using (Finset.abs_sum_le_sum_abs
          (fun r => a r*(J r (k+1)-J r k)) S)
      _ = |b| * (∑ k ∈ Finset.range n,|v (k+1)-v k|) +
          ∑ r ∈ S,|a r| * (∑ k ∈ Finset.range n,|J r (k+1)-J r k|) := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hV (abs_nonneg b))
        (Finset.sum_le_sum fun r hr => by
          simpa using mul_le_mul_of_nonneg_left (hJ' r) (abs_nonneg (a r)))
