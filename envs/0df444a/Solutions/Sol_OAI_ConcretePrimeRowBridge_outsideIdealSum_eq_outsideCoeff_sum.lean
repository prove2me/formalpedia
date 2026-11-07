-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.outsideIdealSum_eq_outsideCoeff_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:20:49.767799+00:00
-- url     : https://prove2.me/submissions/e9994c27-acb6-4839-8d70-bc47a80497e3

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealsUpTo_eq_biUnion_fibers
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
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
namespace ConcretePrimeRowBridge
section
open ActualEisensteinCubic ShortDraftHeckeBridge
open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped Classical
end
open ShortDraftHeckeBridge FiniteSFactor
private theorem normFibers_pairwiseDisjoint (D : ℕ) :
    ((Finset.Icc 1 D : Finset ℕ) : Set ℕ).PairwiseDisjoint
      FiniteSFactor.fiber := by
  intro n hn m hm hnm
  apply Finset.disjoint_left.mpr
  intro I hIn hIm
  exact hnm ((FiniteSFactor.mem_fiber.mp hIn).symm.trans
    (FiniteSFactor.mem_fiber.mp hIm))
open ShortDraftHeckeBridge FiniteSFactor Filter
end ConcretePrimeRowBridge
end
end OAI
end

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
open OAI.ConcretePrimeRowBridge
open ShortDraftHeckeBridge FiniteSFactor
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution
    (S : Finset (Ideal O)) (D : ℕ)
    (w : Ideal O → ℂ) (W : ℕ → ℂ) :
    (∑ I ∈ outsideIdealsUpTo S D,
      w I * W (Ideal.absNorm I)) =
      ∑ n ∈ Finset.Icc 1 D,
        FiniteSFactor.outsideCoeff S w n * W n := by
  classical
  have hsets : outsideIdealsUpTo S D =
      (Finset.Icc 1 D).biUnion (fun n =>
        (FiniteSFactor.fiber n).filter (fun I => ∀ P ∈ S, ¬P ∣ I)) := by
    ext I
    simp [outsideIdealsUpTo, idealsUpTo_eq_biUnion_fibers,
      FiniteSFactor.mem_fiber, Finset.mem_biUnion]
  rw [hsets, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [FiniteSFactor.outsideCoeff, Finset.sum_mul, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro I hI
    rw [FiniteSFactor.mem_fiber.mp hI]
    by_cases hgood : ∀ P ∈ S, ¬P ∣ I <;>
      simp [FiniteSFactor.outsideWeight, hgood]
  · intro n hn m hm hnm
    exact Finset.disjoint_filter_filter
      (normFibers_pairwiseDisjoint D hn hm hnm)
end OAI.ConcretePrimeRowBridge
