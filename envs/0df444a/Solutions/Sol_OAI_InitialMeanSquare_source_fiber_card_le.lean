-- Prove2me | solution 1 for OAI.InitialMeanSquare.source_fiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T09:35:08.088777+00:00
-- url     : https://prove2.me/submissions/95e93fda-f8e5-4581-90d8-58d99876f164

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceTransfer
import Theorems.Thm_OAI_InitialMeanSquare_sourceElementData_injective
import Theorems.Thm_OAI_ConcretePrimeRowBridge_span_idealGenerator
import Theorems.Thm_OAI_InitialMeanSquare_element_fiber_card_le


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic IdealMobiusDivisorSum
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.InitialMeanSquare.O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj
namespace OAI.InitialMeanSquare
theorem _root_.solution (r : O) (s : Finset (SecondExpansionData ι))
    (hs : ∀x∈s,InSecondQuotientSector p r x) (y f : O) (hy : y≠0) :
    (s.filter (fun x => sourceObservation p x=(y,f))).card≤
      (idealDivisors (Ideal.span {y})).card := by
  have hmap : (s.filter (fun x => sourceObservation p x=(y,f))).card≤
      ((s.image (sourceElementData p)).filter (fun x => elementObservation idealGenerator x=(y,f))).card := by
    apply Finset.card_le_card_of_injOn (sourceElementData p)
    · intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,(Finset.mem_filter.mp hx).1,rfl⟩,?_⟩
      exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy he
      exact sourceElementData_injective p hinj r (hs x (Finset.mem_filter.mp hx).1)
        (hs y (Finset.mem_filter.mp hy).1) he
  exact hmap.trans (element_fiber_card_le idealGenerator span_idealGenerator _ y f hy)
end OAI.InitialMeanSquare
