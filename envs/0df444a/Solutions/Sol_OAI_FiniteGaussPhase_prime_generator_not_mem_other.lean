-- Prove2me | solution 1 for OAI.FiniteGaussPhase.prime_generator_not_mem_other
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:10:56.454789+00:00
-- url     : https://prove2.me/submissions/711ea3a5-483a-4e4a-83ac-1e69e69b918a

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization

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
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.FiniteGaussPhase
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.FiniteGaussPhase
theorem _root_.solution {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i k : ι) (hik : i ≠ k) : p k ∉ Ideal.span {p i} := by
  intro h
  have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)
  have ht := (hcop hik).sup_eq
  rw [sup_eq_left.mpr hle] at ht
  exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
end OAI.FiniteGaussPhase
