-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.normalizedPairDensity_eq_primePoolDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T00:51:03.174182+00:00
-- url     : https://prove2.me/submissions/43b0b031-6a5b-4d21-b6e7-5ca10f5c985a

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_RetainedDualBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
import Theorems.Thm_OAI_CanonicalQuadraticSieve_primePoolDensity_eq_support
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealZeroMask_generator_eq_one

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
open scoped BigOperators Classical SchwartzMap
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (I J G : Ideal O)
    (hI : IsCoprime I G) (hJ : IsCoprime J G) :
    normalizedPairDensity I J G = primePoolDensity G := by
  rw [normalizedPairDensity,primePoolDensity_eq_support]
  apply Finset.prod_congr rfl
  intro P hP
  have hPG : P ∣ G := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
    (Multiset.mem_toFinset.mp hP)
  rw [idealZeroMask_generator_eq_one I P (hI.of_isCoprime_of_dvd_right hPG),
    idealZeroMask_generator_eq_one J P (hJ.of_isCoprime_of_dvd_right hPG),one_mul]
end OAI.CanonicalQuadraticSieve
