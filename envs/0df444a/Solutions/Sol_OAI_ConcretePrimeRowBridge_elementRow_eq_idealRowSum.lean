-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.elementRow_eq_idealRowSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:21:39.936791+00:00
-- url     : https://prove2.me/submissions/cfa25608-910f-417a-a22e-0f2393f4e326

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Theorems.Thm_OAI_ConcretePrimeRowBridge_span_idealGenerator
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealGenerator_injective
import Theorems.Thm_OAI_ConcretePrimeRowBridge_columnWeight_idealGenerator

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
open ActualEisensteinCubic ShortDraftHeckeBridge
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (u : O) :
    elementRow F hFpos hFgood χ W u =
      idealRowSum F hFpos hFgood χ W u := by
  classical
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  unfold elementRow idealRowSum
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    rw [columnWeight_idealGenerator, span_idealGenerator]
    rfl
  · intro I hI J hJ h
    exact idealGenerator_injective h
end OAI.ConcretePrimeRowBridge
