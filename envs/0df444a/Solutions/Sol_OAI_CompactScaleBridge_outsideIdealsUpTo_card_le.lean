-- Prove2me | solution 1 for OAI.CompactScaleBridge.outsideIdealsUpTo_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:44:03.444585+00:00
-- url     : https://prove2.me/submissions/c042301c-d5da-43c2-8a6d-2c5c3471e34e

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Theorems.Thm_OAI_CompactScaleBridge_idealsUpTo_card_le

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
theorem _root_.solution (S : Finset (Ideal O)) (N : ℕ) :
    (outsideIdealsUpTo S N).card ≤ 64 * (N + 1) := by
  classical
  calc
    (outsideIdealsUpTo S N).card ≤ (idealsUpTo N).card := by
      apply Finset.card_le_card
      intro I hI
      exact (Finset.mem_filter.mp hI).1
    _ ≤ _ := idealsUpTo_card_le N
end OAI.CompactScaleBridge
