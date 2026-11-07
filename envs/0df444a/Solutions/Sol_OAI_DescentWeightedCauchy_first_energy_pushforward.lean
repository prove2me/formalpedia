-- Prove2me | solution 1 for OAI.DescentWeightedCauchy.first_energy_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:49:53.072701+00:00
-- url     : https://prove2.me/submissions/8efc3111-cc3e-4bed-b302-957fb3ae6ef8

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ReflectedKernel
import Theorems.Thm_OAI_DescentWeightedCauchy_bounded_energy_pushforward
import Theorems.Thm_OAI_DescentWeightedCauchy_firstRowMap_fiber_card_le

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
    (s : Finset (Ideal O × Ideal O)) (t : Finset (Ideal O))
    (E : Ideal O) (w : Ideal O × Ideal O → ℂ) (P : Ideal O → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hmap : ∀ x ∈ s, firstRowMap E x ∈ t)
    (ht : ∀ Y ∈ t, Y ≠ ⊥) (hw : ∀ x ∈ s, ‖w x‖ ≤ C) :
    (∑ x ∈ s, ‖w x‖ * ‖P (firstRowMap E x)‖ ^ 2) ≤
      ∑ Y ∈ t, C * (IdealMobiusDivisorSum.idealDivisors Y).card * ‖P Y‖ ^ 2 := by
  apply (bounded_energy_pushforward s t (firstRowMap E) w P C hmap hw).trans
  apply Finset.sum_le_sum
  intro Y hY
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast firstRowMap_fiber_card_le s E Y (ht Y hY)) hC)
    (sq_nonneg _)
end OAI.DescentWeightedCauchy
