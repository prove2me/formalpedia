-- Prove2me | solution 1 for OAI.InitialMeanSquare.element_fiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:29:13.877745+00:00
-- url     : https://prove2.me/submissions/4b9f0c3a-2e08-4c74-9202-cc42bfab8a69

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_UniformTailBounds
import Theorems.Thm_OAI_InitialMeanSquare_element_divisor_injective_on_fiber

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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.InitialMeanSquare
open IdealMobiusDivisorSum
namespace OAI.InitialMeanSquare
theorem _root_.solution (gen : Ideal O→O) (hgen : ∀D,Ideal.span {gen D}=D)
    (s : Finset ElementDatum) (y f : O) (hy : y≠0) :
    (s.filter (fun x => elementObservation gen x=(y,f))).card≤(idealDivisors (Ideal.span {y})).card := by
  have hyI : (Ideal.span {y}:Ideal O)≠0 := by intro hz; exact hy (Ideal.span_singleton_eq_bot.mp hz)
  apply Finset.card_le_card_of_injOn ElementDatum.divisor
  · intro x hx
    change x.divisor∈idealDivisors (Ideal.span {y})
    rw [mem_idealDivisors hyI]
    have he : elementRow gen x=y := congrArg Prod.fst (Finset.mem_filter.mp hx).2
    rw [←he,elementRow,←Ideal.span_singleton_mul_span_singleton,hgen]
    exact dvd_mul_right _ _
  · intro x hx z hz he
    exact element_divisor_injective_on_fiber gen y f hy (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hz).2 he
end OAI.InitialMeanSquare
