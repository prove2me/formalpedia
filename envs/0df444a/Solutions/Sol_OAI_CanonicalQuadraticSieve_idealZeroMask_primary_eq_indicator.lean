-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.idealZeroMask_primary_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T19:52:11.789427+00:00
-- url     : https://prove2.me/submissions/732e06f2-cc75-4f67-ba10-81ad79a38773

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealZeroMask_generator_eq_indicator
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealZeroMask_span_eq
import Theorems.Thm_OAI_CanonicalQuadraticSieve_supported_primaryGenerator_ne_zero
import Theorems.Thm_OAI_ConcretePrimeRowBridge_span_idealGenerator


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
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (D B : Ideal O) (hD : D≠0) (hB : Supported B) :
    idealZeroMask D (primaryGenerator B) = if IsCoprime B D then 1 else 0 := by
  have he : Ideal.span {primaryGenerator B}=Ideal.span {idealGenerator B} := by
    rw [(primaryGenerator_spec B (supported_primaryGenerator_ne_zero B hB)).1,span_idealGenerator]
  rw [idealZeroMask_span_eq D _ _ he,idealZeroMask_generator_eq_indicator D B hD]
end OAI.CanonicalQuadraticSieve
