-- Prove2me | solution 1 for OAI.CubicEisenstein.euclideanInversion_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:29:31.69912+00:00
-- url     : https://prove2.me/submissions/1b04c4ce-c49d-44f6-aa06-2795351e3b33

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonComparison
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins
import Theorems.Thm_OAI_CubicEisenstein_euclideanInversion_apply
import Theorems.Thm_OAI_CubicEisenstein_euclideanUpperHalf_ne_zero

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
open Filter MeasureTheory EuclideanGeometry
open scoped BigOperators Classical Topology InnerProductSpace ENNReal
open OAI.CubicEisenstein
namespace OAI.CubicEisenstein
theorem _root_.solution (p : EuclideanSpatial) (hp : p∈euclideanUpperHalf) :
    euclideanInversion p∈euclideanUpperHalf := by
  change 0<euclideanInversion p 2
  rw [euclideanInversion_apply]
  exact mul_pos (sq_pos_of_pos (one_div_pos.mpr (norm_pos_iff.mpr (euclideanUpperHalf_ne_zero p hp)))) hp
end OAI.CubicEisenstein
