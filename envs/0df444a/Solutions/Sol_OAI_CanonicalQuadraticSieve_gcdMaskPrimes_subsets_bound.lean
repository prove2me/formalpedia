-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.gcdMaskPrimes_subsets_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:51:31.065463+00:00
-- url     : https://prove2.me/submissions/293ca41b-d0f4-4c0c-8c23-18c6735d8d71

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedNormWeights
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrincipalTruncation
import Theorems.Thm_OAI_CanonicalQuadraticSieve_gcdMaskPrimes_card_le
import Theorems.Thm_OAI_IdealCoprimeSieveOperator_support_card_bound


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
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson TruncatedPrincipalPoisson IdealCoprimeSieveOperator
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) (D : Ideal O) (hD : D ≠ 0) :
    (2 : ℝ) ^ (gcdMaskPrimes D).card ≤
      4 * supportConstant ε hε * (Ideal.absNorm D : ℝ) ^ ε := by
  calc
    _ ≤ (2 : ℝ) ^ (2 + (IdealMobiusDivisorSum.primeSupport D).card) :=
      pow_le_pow_right₀ (by norm_num) (gcdMaskPrimes_card_le D)
    _ = 4 * (2 : ℝ) ^ (IdealMobiusDivisorSum.primeSupport D).card := by rw [pow_add]; norm_num
    _ ≤ 4 * (supportConstant ε hε * (Ideal.absNorm D : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (support_card_bound ε hε D hD) (by norm_num)
    _ = _ := by ring
end OAI.CanonicalQuadraticSieve
