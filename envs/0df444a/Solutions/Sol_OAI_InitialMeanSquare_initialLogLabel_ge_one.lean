-- Prove2me | solution 1 for OAI.InitialMeanSquare.initialLogLabel_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:07:44.117044+00:00
-- url     : https://prove2.me/submissions/7b38f083-8922-4152-b6c5-c44289f99aa7

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_RetainedDensity
import Theorems.Thm_OAI_SecondPassArithmetic_normLogScale_ge_one


set_option autoImplicit false
open OAI
noncomputable section
open OAI.InitialMeanSquare
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (primeProductNorm)
namespace OAI.InitialMeanSquare
theorem _root_.solution (j : SecondLogIndex) : 1 ≤ initialLogLabel j :=
  one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _))
    (Real.one_le_exp (by norm_num))
end OAI.InitialMeanSquare
