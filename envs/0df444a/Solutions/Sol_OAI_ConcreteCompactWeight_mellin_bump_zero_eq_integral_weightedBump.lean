-- Prove2me | solution 1 for OAI.ConcreteCompactWeight.mellin_bump_zero_eq_integral_weightedBump
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:55:33.347666+00:00
-- url     : https://prove2.me/submissions/eb45c74c-1350-4817-92a2-578949bde66c

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Theorems.Thm_OAI_ConcreteCompactWeight_bump_support
import Theorems.Thm_OAI_ConcreteCompactWeight_positiveExtension_eq
import Theorems.Thm_OAI_ConcreteCompactWeight_weightedBump_eq_zero_of_nonpos
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
theorem _root_.solution :
    mellin (fun y : ℝ => (bump y : ℂ)) 0 =
      (∫ y : ℝ, weightedBump y : ℝ) := by
  rw [mellin]
  have hpoint : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ ((0 : ℂ) - 1) • (bump y : ℂ) =
        (weightedBump y : ℂ) := by
    intro y hy
    by_cases hy1 : y ≤ 1
    · simp [weightedBump, bump_support y (Or.inl hy1)]
    · have hgy : positiveExtension y = y :=
        positiveExtension_eq y (le_of_lt (lt_of_not_ge hy1))
      simp [weightedBump, hgy, Complex.cpow_neg_one, smul_eq_mul,
        div_eq_mul_inv, mul_comm]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => hpoint y hy)]
  rw [integral_complex_ofReal]
  congr 1
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    exact weightedBump_eq_zero_of_nonpos y (le_of_not_gt hy))
end OAI.ConcreteCompactWeight
