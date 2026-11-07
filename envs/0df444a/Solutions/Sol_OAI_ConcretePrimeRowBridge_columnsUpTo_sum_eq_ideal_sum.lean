-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.columnsUpTo_sum_eq_ideal_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:21:40.625846+00:00
-- url     : https://prove2.me/submissions/3beb528d-aff5-4173-b364-e064d1703c94

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
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
theorem _root_.solution {q D : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) :
    (∑ x ∈ columnsUpTo D, columnWeight χ W x) =
      ∑ I ∈ idealsUpTo D,
        baseChangeWeight χ I * W (Ideal.absNorm I) := by
  classical
  rw [columnsUpTo, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    exact columnWeight_idealGenerator χ W I
  · intro I hI J hJ h
    exact idealGenerator_injective h
end OAI.ConcretePrimeRowBridge
