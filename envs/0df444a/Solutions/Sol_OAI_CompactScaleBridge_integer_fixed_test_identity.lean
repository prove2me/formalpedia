-- Prove2me | solution 1 for OAI.CompactScaleBridge.integer_fixed_test_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:43:10.431754+00:00
-- url     : https://prove2.me/submissions/900afc74-7993-42df-ae00-20c5b8c3d265

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Theorems.Thm_OAI_ConcretePrimeRowBridge_outsideIdealSum_eq_outsideCoeff_sum
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
open OAI.CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge
namespace OAI.CompactScaleBridge
theorem _root_.solution
    (S : Finset (Ideal O)) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℝ → ℂ) (m : ℕ) (hm : 0 < m) :
    (∑ I ∈ outsideIdealsUpTo S (2 * m),
      baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))) =
    ∑ n ∈ Finset.Icc 1 (2 * m),
      FiniteSFactor.outsideCoeff S (baseChangeWeight χ) n *
        (fun y : ℝ => W (2 * y)) ((n : ℝ) / (2 * m : ℕ)) := by
  convert outsideIdealSum_eq_outsideCoeff_sum S (2 * m)
    (baseChangeWeight χ) (fun n => W ((n : ℝ) / (m : ℝ))) using 1
  simp only
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  push_cast
  field_simp
end OAI.CompactScaleBridge
