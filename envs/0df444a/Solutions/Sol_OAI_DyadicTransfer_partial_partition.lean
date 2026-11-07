-- Prove2me | solution 1 for OAI.DyadicTransfer.partial_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:15:29.048648+00:00
-- url     : https://prove2.me/submissions/65669741-665d-4bee-9ef6-947749c7350e

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
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
theorem _root_.solution (φ : ℝ → ℂ) (x : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1),
      annularCutoff φ (x / (2 : ℝ) ^ k)) =
      φ (x / (2 : ℝ) ^ K) - φ (2 * x) := by
  induction K with
  | zero =>
      simp [annularCutoff]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      unfold annularCutoff
      have hpow : (2 : ℝ) ^ (K + 1) ≠ 0 := by positivity
      have hshift : 2 * (x / (2 : ℝ) ^ (K + 1)) = x / (2 : ℝ) ^ K := by
        rw [pow_succ]
        field_simp
      rw [hshift]
      ring
end OAI.DyadicTransfer
