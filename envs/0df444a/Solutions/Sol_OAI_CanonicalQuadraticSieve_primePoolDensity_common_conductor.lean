-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.primePoolDensity_common_conductor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T00:50:38.104178+00:00
-- url     : https://prove2.me/submissions/68d032ff-ada5-4dc1-bad7-6e32319e2c5a

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_RetainedDualBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
import Theorems.Thm_OAI_CanonicalQuadraticSieve_primePoolDensity_mul

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
open ActualEisensteinCubic
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (I J G : Ideal O)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hG : G ≠ 0)
    (hIJ : IsCoprime I J) (hGI : IsCoprime G I) (hGJ : IsCoprime G J) :
    primePoolDensity (G*(I*J)) = primePoolDensity G*(primePoolDensity I*primePoolDensity J) := by
  rw [primePoolDensity_mul G (I*J) hG (mul_ne_zero hI hJ) (hGI.mul_right hGJ),
    primePoolDensity_mul I J hI hJ hIJ]
end OAI.CanonicalQuadraticSieve
