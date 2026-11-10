-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.liftingDividedCoefficient_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:02:12.780056+00:00
-- url     : https://prove2.me/submissions/01a44cf0-e884-4420-af3f-43dadee98268

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealQuotient_mul
import Theorems.Thm_OAI_FiniteSieveRestriction_extendByZero_zero


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CanonicalQuadraticSieve
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
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
open FiniteSieveRestriction
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (N : ℝ) (a : idealRange N → ℂ)
    (J : idealRange N) (hJ : liftingDividedCoefficient N a J≠0) : IsCoprime liftingPrime J.val := by
  classical
  have hmem : J∈(Finset.univ : Finset (liftingDivisibleColumns N)).image (liftingQuotientColumn N) := by
    by_contra hn
    exact hJ (extendByZero_zero _ _ _ _ hn)
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hmem
  have hdiv := (Finset.mem_filter.mp I.property).2
  have hsf : Squarefree (liftingPrime*idealQuotient liftingPrime I.val.val) := by
    rw [idealQuotient_mul hdiv]
    exact (mem_idealRange.mp I.val.property).1.2.1
  exact ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp hsf).1
end OAI.CanonicalQuadraticSieve
