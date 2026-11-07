-- Prove2me | solution 1 for OAI.DyadicTransfer.finite_exp_reassembly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:19:44.004478+00:00
-- url     : https://prove2.me/submissions/593bc2d9-4179-49c6-8d36-d85a6c7d4797

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Theorems.Thm_OAI_DyadicTransfer_partition_nat
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
theorem _root_.solution (a : ℕ → ℂ) (φ : ℝ → ℂ)
    (ha0 : a 0 = 0)
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → φ y = 0)
    (D : ℝ) (N K : ℕ)
    (hK : ∀ n ∈ Finset.range N, 1 ≤ n → (n : ℝ) ≤ (2 : ℝ) ^ K) :
    (∑ n ∈ Finset.range N, a n * Real.exp (-(n : ℝ) / D)) =
      ∑ k ∈ Finset.range (K + 1),
        ∑ n ∈ Finset.range N,
          a n * expAnnularTest φ D k ((n : ℝ) / (2 : ℝ) ^ k) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [ha0, expAnnularTest, annularCutoff]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hpart := partition_nat φ hsmall hlarge n K hn1 (hK n hn hn1)
    simp_rw [expAnnularTest]
    have hexp (k : ℕ) :
        Real.exp (-((2 : ℝ) ^ k / D) * ((n : ℝ) / (2 : ℝ) ^ k)) =
          Real.exp (-(n : ℝ) / D) := by
      congr 1
      have hpow : (2 : ℝ) ^ k ≠ 0 := by positivity
      field_simp
    simp_rw [hexp]
    rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, hpart]
    simp
end OAI.DyadicTransfer
