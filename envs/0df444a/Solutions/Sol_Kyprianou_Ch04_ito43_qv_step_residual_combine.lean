-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_step_residual_combine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:31:03.167719+00:00
-- url     : https://prove2.me/submissions/6622528f-6390-4b72-aaef-54cdd1b557e0

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Ring
open MeasureTheory Filter Set
set_option autoImplicit false
/-- Separate the three weighted approximation errors and apply the triangle inequality. -/
theorem solution
    (σ δ T J Q A B G : ℝ) (hσ : 0 ≤ σ)
    (m : ℕ) (c a j q : ℕ → ℝ)
    (ha : |A-∑ i ∈ Finset.range m, c i*a i| ≤ δ*T)
    (hb : |B-∑ i ∈ Finset.range m, c i*j i| ≤ δ*J)
    (hg : |G-∑ i ∈ Finset.range m, c i*q i| ≤ δ*Q) :
    |σ*A+B-G - ∑ i ∈ Finset.range m, c i*(σ*a i+j i-q i)| ≤
      δ*(σ*T+J+Q) := by
  have hσsum : (∑ i ∈ Finset.range m, c i*(σ*a i)) =
      σ*(∑ i ∈ Finset.range m, c i*a i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum : (∑ i ∈ Finset.range m, c i*(σ*a i+j i-q i)) =
      σ*(∑ i ∈ Finset.range m, c i*a i) +
      (∑ i ∈ Finset.range m, c i*j i) - (∑ i ∈ Finset.range m, c i*q i) := by
    simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,hσsum]
  rw [hsum]
  let x := A-∑ i ∈ Finset.range m, c i*a i
  let y := B-∑ i ∈ Finset.range m, c i*j i
  let z := G-∑ i ∈ Finset.range m, c i*q i
  have heq : σ*A+B-G - (σ*(∑ i ∈ Finset.range m, c i*a i) +
      (∑ i ∈ Finset.range m, c i*j i) - (∑ i ∈ Finset.range m, c i*q i)) =
      σ*x+y+(-z) := by dsimp [x,y,z]; ring
  rw [heq]
  calc
    _ ≤ |σ*x+y| + |-z| := abs_add_le _ _
    _ ≤ |σ*x| + |y| + |-z| := add_le_add (abs_add_le _ _) le_rfl
    _ = σ*|x|+|y|+|z| := by rw [abs_mul,abs_of_nonneg hσ,abs_neg]
    _ ≤ σ*(δ*T)+δ*J+δ*Q :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left ha hσ) hb) hg
    _ = _ := by ring
