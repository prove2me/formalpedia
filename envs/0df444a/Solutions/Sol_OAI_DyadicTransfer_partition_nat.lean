-- Prove2me | solution 1 for OAI.DyadicTransfer.partition_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:17:02.348535+00:00
-- url     : https://prove2.me/submissions/574eeb54-f793-4035-9e23-37711f4ace69

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Theorems.Thm_OAI_DyadicTransfer_partial_partition
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
theorem _root_.solution (φ : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → φ y = 0)
    (n K : ℕ) (hn : 1 ≤ n) (hK : (n : ℝ) ≤ (2 : ℝ) ^ K) :
    (∑ k ∈ Finset.range (K + 1),
      annularCutoff φ ((n : ℝ) / (2 : ℝ) ^ k)) = 1 := by
  rw [partial_partition]
  have hpow : 0 < (2 : ℝ) ^ K := by positivity
  have hnsmall : (n : ℝ) / (2 : ℝ) ^ K ≤ 1 :=
    (div_le_iff₀ hpow).mpr (by simpa using hK)
  rw [hsmall _ hnsmall, hlarge]
  · ring
  · exact_mod_cast (show (2 : ℕ) ≤ 2 * n by omega)
end OAI.DyadicTransfer
