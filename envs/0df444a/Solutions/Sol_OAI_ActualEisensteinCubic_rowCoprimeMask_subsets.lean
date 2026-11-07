-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.rowCoprimeMask_subsets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:55:22.337855+00:00
-- url     : https://prove2.me/submissions/c8048138-e26d-4c5e-81b3-1f9d9f383af1

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
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
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
namespace ActualEisensteinCubic
section
open scoped ComplexConjugate
end
private theorem mask_powerset {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (if ∃ i ∈ S, p i then (0 : ℂ) else 1) =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        if ∀ i ∈ E, p i then 1 else 0 := by
  have hprod : (if ∃ i ∈ S, p i then (0 : ℂ) else 1) =
      ∏ i ∈ S, (1 - if p i then (1 : ℂ) else 0) := by
    by_cases h : ∃ i ∈ S, p i
    · rw [if_pos h]
      obtain ⟨i, hi, hp⟩ := h
      symm
      apply Finset.prod_eq_zero hi
      simp [hp]
    · rw [if_neg h]
      symm
      apply Finset.prod_eq_one
      intro i hi
      simp [show ¬p i from fun hp => h ⟨i, hi, hp⟩]
  rw [hprod, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro E hE
  simp only [Finset.prod_const_one, mul_one]
  congr 1
  by_cases h : ∀ i ∈ E, p i
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h i hi]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi, hp⟩ := h
    apply Finset.prod_eq_zero hi
    simp [hp]
end ActualEisensteinCubic
namespace ConcretePrimeRowBridge
section
open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped BigOperators Classical
end
open ActualEisensteinCubic
end ConcretePrimeRowBridge
namespace EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace
end EisensteinSchwartzPoisson
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
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (u : O) :
    rowCoprimeMask P S u =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        if ∀ i ∈ E, u ∈ P i then 1 else 0 := by
  classical
  exact mask_powerset S (fun i => u ∈ P i)
end OAI.ActualEisensteinCubic
