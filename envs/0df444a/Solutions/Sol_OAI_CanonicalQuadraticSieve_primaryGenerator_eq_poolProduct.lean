-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.primaryGenerator_eq_poolProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:43:49.628828+00:00
-- url     : https://prove2.me/submissions/3eef9fca-a23d-47ce-baad-7fc87dd7fa01

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GcdReduction
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowMajorants
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrimePools
import Theorems.Thm_OAI_CanonicalQuadraticSieve_primaryPrime_eq_primaryGenerator
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealSupport_product_eq


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
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hIF : I ∈ F) :
    primaryGenerator I = ∏ i ∈ idealSupport F I, poolPrimary F i := by
  calc
    _ = primaryGenerator (∏ i ∈ idealSupport F I, i.val) :=
      congrArg primaryGenerator (idealSupport_product_eq F hIF (hF I hIF).2.1).symm
    _ = ∏ i ∈ idealSupport F I, primaryGenerator i.val := by
      change primaryGeneratorHom (∏ i ∈ idealSupport F I, i.val) =
        ∏ i ∈ idealSupport F I, primaryGeneratorHom i.val
      rw [map_prod]
    _ = _ := Finset.prod_congr rfl (fun i hi => (primaryPrime_eq_primaryGenerator i.val).symm)
end OAI.CanonicalQuadraticSieve
