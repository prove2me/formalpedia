-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_product_grid_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:51:16.827026+00:00
-- url     : https://prove2.me/submissions/1317c1f7-6dc4-48e2-a577-53e6603f0675

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false

/-- A product of two bounded grid factors has variation controlled
by the separate factor variation and their uniform bounds. -/
theorem solution
    (a b : Nat → Real) (C : Real) (n : Nat)
    (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ 1)
    (hb : ∀ i, |b i| ≤ C)
    (hVA : (∑ i ∈ Finset.range n, |a (i+1) - a i|) ≤ 1)
    (hVB : (∑ i ∈ Finset.range n, |b (i+1) - b i|) ≤ C) :
    (∑ i ∈ Finset.range n,
      |a (i+1) * b (i+1) - a i * b i|) ≤ 2 * C := by
  have hCell (i : Nat) :
      |a (i+1) * b (i+1) - a i * b i|
        ≤ C * |a (i+1) - a i| + |b (i+1) - b i| := by
    have heq :
        a (i+1) * b (i+1) - a i * b i =
          (a (i+1) - a i) * b (i+1) +
            a i * (b (i+1) - b i) := by ring
    rw [heq]
    calc
      |(a (i+1) - a i) * b (i+1) +
          a i * (b (i+1) - b i)|
        ≤ |(a (i+1) - a i) * b (i+1)| +
            |a i * (b (i+1) - b i)| := abs_add_le _ _
      _ = |a (i+1) - a i| * |b (i+1)| +
            |a i| * |b (i+1) - b i| := by rw [abs_mul, abs_mul]
      _ ≤ C * |a (i+1) - a i| + |b (i+1) - b i| := by
        have h1 := mul_le_mul_of_nonneg_left (hb (i+1))
          (abs_nonneg (a (i+1) - a i))
        have h2 := mul_le_mul_of_nonneg_right (ha i)
          (abs_nonneg (b (i+1) - b i))
        nlinarith
  calc
    (∑ i ∈ Finset.range n,
      |a (i+1) * b (i+1) - a i * b i|)
        ≤ ∑ i ∈ Finset.range n,
          (C * |a (i+1) - a i| + |b (i+1) - b i|) :=
          Finset.sum_le_sum (fun i _ => hCell i)
    _ = C * (∑ i ∈ Finset.range n, |a (i+1) - a i|) +
          (∑ i ∈ Finset.range n, |b (i+1) - b i|) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ C * 1 + C := add_le_add
        (mul_le_mul_of_nonneg_left hVA hC) hVB
    _ = 2 * C := by ring
