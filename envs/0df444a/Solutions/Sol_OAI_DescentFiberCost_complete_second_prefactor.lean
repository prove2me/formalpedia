-- Prove2me | solution 1 for OAI.DescentFiberCost.complete_second_prefactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:15:52.748574+00:00
-- url     : https://prove2.me/submissions/5a78749f-f3e0-4d32-8904-23cdf3f1e7df

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MainTermDifference
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_InverseContour

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
open OAI.DescentFiberCost
open scoped BigOperators Classical
open ConcretePrimeRowBridge
namespace OAI.DescentFiberCost
theorem _root_.solution
    (K ell B F A C d J g e v t w c : ℝ)
    (hK : K ≠ 0) (hell : ell ≠ 0) (hB : B ≠ 0) (hF : F ≠ 0)
    (hC : C ≠ 0) (hd : d ≠ 0) (hJ : J ≠ 0)
    (hg : g ≠ 0) (he : e ≠ 0) (hv : v ≠ 0) (hc : c ≠ 0)
    (Li : ℝ) (hLi : Li ≠ 0) :
    (K * A * C / (d * ell ^ 2 * B ^ 2 * F * c)) *
      ((ell ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J)) * g / (e * Li)) *
      ((B * c / J) * t * w) *
      ((Li / (g * v)) * (J * C * e * v)) =
      (B * F * A * t * w) * B ^ 2 / J := by
  field_simp
end OAI.DescentFiberCost
