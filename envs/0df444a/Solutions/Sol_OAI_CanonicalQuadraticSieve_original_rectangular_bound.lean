-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.original_rectangular_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:23:58.701209+00:00
-- url     : https://prove2.me/submissions/70e75662-f03c-44ef-8a7d-a16cfe748d88

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DivisorBlocks
import Theorems.Thm_OAI_CanonicalQuadraticSieve_originalBlock_le_quotientBlock
import Theorems.Thm_OAI_IdealDivisorBilinearBlocks_blockValue_nonneg


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
open OAI.CanonicalQuadraticSieve
open IdealDivisorBilinearBlocks CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (a : n → ℂ) (b : p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, originalBlock rows left right a b D E) ^ 2 ≤
      (∑ D ∈ S, ∑ E ∈ T, quotientBlock rows left right a b D E) ^ 2 := by
  apply pow_le_pow_left₀
  · exact Finset.sum_nonneg (fun D _ => Finset.sum_nonneg (fun E _ =>
      blockValue_nonneg left right _ _ a b D E))
  · apply Finset.sum_le_sum
    intro D hD
    exact Finset.sum_le_sum (fun E hE => originalBlock_le_quotientBlock
      rows left right hleft hright a b D E)
end OAI.CanonicalQuadraticSieve
