-- Prove2me | solution 1 for OAI.IdealCoprimeSieveOperator.primeSupport_disjoint_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:14:20.582692+00:00
-- url     : https://prove2.me/submissions/e1353857-32e3-4674-b62a-6c74e2e3bdaa

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_UniformKernelBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization

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
open scoped BigOperators Classical
open OAI.IdealCoprimeSieveOperator
open IdealMobiusDivisorSum CoprimeSieveOperator FiniteSieveOperator
open UniqueFactorizationMonoid
namespace OAI.IdealCoprimeSieveOperator
theorem _root_.solution {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0) :
    Disjoint (primeSupport I) (primeSupport J) ↔ IsCoprime I J := by
  constructor
  · intro h
    have hr : IsRelPrime I J := (isRelPrime_iff_no_prime_factors hI).mpr (by
      intro P hPI hPJ hP
      apply Finset.disjoint_left.mp h
      · apply Multiset.mem_toFinset.mpr
        exact (Ideal.mem_normalizedFactors_iff hI).mpr
          ⟨Ideal.isPrime_of_prime hP, Ideal.dvd_iff_le.mp hPI⟩
      · apply Multiset.mem_toFinset.mpr
        exact (Ideal.mem_normalizedFactors_iff hJ).mpr
          ⟨Ideal.isPrime_of_prime hP, Ideal.dvd_iff_le.mp hPJ⟩)
    apply Ideal.isCoprime_iff_gcd.mpr
    exact associated_iff_eq.mp (associated_one_iff_isUnit.mpr (gcd_isUnit_iff_isRelPrime.mpr hr))
  · intro h
    exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors h.isRelPrime)
end OAI.IdealCoprimeSieveOperator
