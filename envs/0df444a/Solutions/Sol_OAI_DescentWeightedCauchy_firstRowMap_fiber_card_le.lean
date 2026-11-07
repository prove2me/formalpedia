-- Prove2me | solution 1 for OAI.DescentWeightedCauchy.firstRowMap_fiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:48:43.903524+00:00
-- url     : https://prove2.me/submissions/feec203f-cabb-4c0d-bc91-ff3ebedcf776

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ReflectedKernel
import Theorems.Thm_OAI_DescentWeightedCauchy_firstRowMap_fst_dvd
import Theorems.Thm_OAI_DescentWeightedCauchy_firstRowMap_fst_injective_on_fiber

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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
open scoped BigOperators Classical
open OAI.DescentWeightedCauchy
namespace OAI.DescentWeightedCauchy
theorem _root_.solution
    (s : Finset (Ideal O × Ideal O)) (E Y : Ideal O) (hY : Y ≠ ⊥) :
    (s.filter (fun x => firstRowMap E x = Y)).card ≤
      (IdealMobiusDivisorSum.idealDivisors Y).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    change x.1 ∈ IdealMobiusDivisorSum.idealDivisors Y
    rw [IdealMobiusDivisorSum.mem_idealDivisors hY]
    rw [← (Finset.mem_filter.mp hx).2]
    exact firstRowMap_fst_dvd E x
  · intro x hx z hz he
    exact firstRowMap_fst_injective_on_fiber s E Y hY
      (Finset.mem_filter.mp hx) (Finset.mem_filter.mp hz) he
end OAI.DescentWeightedCauchy
