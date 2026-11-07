-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.idealSupport_product_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:52.759201+00:00
-- url     : https://prove2.me/submissions/7db23060-4653-406d-8176-e796b177aeab

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_RadialFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealSupport_image_eq_factors

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
open OAI.ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution
    (F : Finset (Ideal O)) {I : Ideal O} (hI : I ∈ F) (hsI : Squarefree I) :
    (∏ i ∈ idealSupport F I, i.val) = I := by
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
    hsI.ne_zero).mp hsI
  calc
    _ = ∏ P ∈ (idealSupport F I).image Subtype.val, P := by
      rw [Finset.prod_image]
      exact fun a ha b hb h => Subtype.val_injective h
    _ = ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset, P := by
      rw [idealSupport_image_eq_factors F hI]
    _ = (UniqueFactorizationMonoid.normalizedFactors I).prod := by
      change ((UniqueFactorizationMonoid.normalizedFactors I).toFinset.val.map id).prod = _
      rw [Multiset.map_id, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
    _ = I := Ideal.prod_normalizedFactors_eq_self hsI.ne_zero
end OAI.ConcretePrimeRowBridge
