-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.productColumnCoefficient_row_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:21:19.447234+00:00
-- url     : https://prove2.me/submissions/71de36f0-4a35-4c52-b75f-a54a24670baf

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns

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
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (k : Ideal O) :
    (∑n∈S,∑b∈T,quadraticRow k (primaryGenerator (n*b))*β n b)=
    ∑I∈(S×ˢT).image (fun p => p.1*p.2),quadraticRow k (primaryGenerator I)*productColumnCoefficient S T β I := by
  rw [←Finset.sum_product (f := fun p : Ideal O×Ideal O => quadraticRow k (primaryGenerator (p.1*p.2))*β p.1 p.2)]
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun p (hp : p∈S×ˢT) => Finset.mem_image_of_mem (fun p : Ideal O×Ideal O => p.1*p.2) hp)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [productColumnCoefficient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]
end OAI.CanonicalQuadraticSieve
