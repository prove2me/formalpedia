-- Prove2me | solution 1 for OAI.ConcreteCompactWeight.positiveExtension_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:52:46.3268+00:00
-- url     : https://prove2.me/submissions/64268157-1d7b-4962-a3f6-8d9791a9bd01

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights

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
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ConcreteCompactWeight
namespace OAI.ConcreteCompactWeight
theorem _root_.solution (y : ℝ) : 0 < positiveExtension y := by
  unfold positiveExtension
  by_cases hhalf : y ≤ 1 / 2
  · have ht : 2 * y - 1 ≤ 0 := by linarith
    rw [Real.smoothTransition.zero_of_nonpos ht]
    norm_num
  · by_cases hone : 1 ≤ y
    · have ht : 1 ≤ 2 * y - 1 := by linarith
      rw [Real.smoothTransition.one_of_one_le ht]
      linarith
    · have hle := Real.smoothTransition.le_one (2 * y - 1)
      have hnonneg := Real.smoothTransition.nonneg (2 * y - 1)
      have hprod : (1 - y) * Real.smoothTransition (2 * y - 1) ≤ 1 - y := by
        exact (mul_le_mul_of_nonneg_left hle (by linarith)).trans_eq (mul_one _)
      nlinarith
end OAI.ConcreteCompactWeight
