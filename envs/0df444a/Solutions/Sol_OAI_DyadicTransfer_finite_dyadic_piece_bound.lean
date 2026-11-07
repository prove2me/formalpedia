-- Prove2me | solution 1 for OAI.DyadicTransfer.finite_dyadic_piece_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:15:58.7961+00:00
-- url     : https://prove2.me/submissions/d35c65f0-d81b-419f-bfcb-ec9370fb2fab

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open OAI.DyadicTransfer
namespace OAI.DyadicTransfer
theorem _root_.solution
    (F : ℕ → ℂ) (C r : ℝ) (hC : 0 ≤ C) (hr : 1 < r)
    (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ m, 0 ≤ b m)
    (N M : ℕ)
    (hlow : ∀ k ≤ N, ‖F k‖ ≤ C * r ^ k)
    (hhigh : ∀ m, ‖F (N + 1 + m)‖ ≤ C * r ^ N * b m) :
    ‖∑ k ∈ Finset.range (N + 1 + M), F k‖ ≤
      C * (r ^ (N + 1) / (r - 1) + r ^ N * ∑' m, b m) := by
  have hr0 : 0 ≤ r := by linarith
  have hrden : 0 < r - 1 := by linarith
  have hlowSum :
      ‖∑ k ∈ Finset.range (N + 1), F k‖ ≤
        C * (r ^ (N + 1) / (r - 1)) := by
    calc
      ‖∑ k ∈ Finset.range (N + 1), F k‖ ≤
          ∑ k ∈ Finset.range (N + 1), ‖F k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (N + 1), C * r ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        exact hlow k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      _ = C * ((r ^ (N + 1) - 1) / (r - 1)) := by
        rw [← Finset.mul_sum, geom_sum_eq (ne_of_gt hr)]
      _ ≤ C * (r ^ (N + 1) / (r - 1)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact div_le_div_of_nonneg_right (by linarith) hrden.le
  have hhighSum :
      ‖∑ m ∈ Finset.range M, F (N + 1 + m)‖ ≤
        C * r ^ N * ∑' m, b m := by
    calc
      ‖∑ m ∈ Finset.range M, F (N + 1 + m)‖ ≤
          ∑ m ∈ Finset.range M, ‖F (N + 1 + m)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.range M, C * r ^ N * b m := by
        apply Finset.sum_le_sum
        intro m _
        exact hhigh m
      _ = C * r ^ N * ∑ m ∈ Finset.range M, b m := by
        rw [← Finset.mul_sum]
      _ ≤ C * r ^ N * ∑' m, b m := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (pow_nonneg hr0 N))
        exact hb.sum_le_tsum _ (fun m _ => hb0 m)
  rw [Finset.sum_range_add]
  calc
    ‖(∑ k ∈ Finset.range (N + 1), F k) +
      ∑ m ∈ Finset.range M, F (N + 1 + m)‖ ≤
        ‖∑ k ∈ Finset.range (N + 1), F k‖ +
          ‖∑ m ∈ Finset.range M, F (N + 1 + m)‖ := norm_add_le _ _
    _ ≤ C * (r ^ (N + 1) / (r - 1)) + C * r ^ N * ∑' m, b m :=
      add_le_add hlowSum hhighSum
    _ = C * (r ^ (N + 1) / (r - 1) + r ^ N * ∑' m, b m) := by ring
end OAI.DyadicTransfer
