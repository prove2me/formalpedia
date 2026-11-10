-- Prove2me | solution 1 for OAI.CompletedGauss.completed_scaled_shape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:29:18.869201+00:00
-- url     : https://prove2.me/submissions/b431eea7-27cb-4169-b01f-88289034bb63

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
namespace OAI.CompletedGauss
theorem _root_.solution (ε k y H c B : ℝ) (hε : 0≤ε) (hk : 0<k)
    (hy : 0<y) (hH : 0<H) (hc : 0<c) (hcB : c≤B) (hB : 1≤B) :
    (k*(c*y))^ε*(k+c*y)/H≤B^(ε+1)*((k*y)^ε*(k+y)/H) := by
  have hB0 : 0<B := by linarith
  have hp : (k*(c*y))^ε≤B^ε*(k*y)^ε := by
    rw [show k*(c*y)=c*(k*y) by ring,Real.mul_rpow hc.le (mul_pos hk hy).le]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hc.le hcB hε) (by positivity)
  have hs : k+c*y≤B*(k+y) := by nlinarith
  calc
    _ ≤ (B^ε*(k*y)^ε)*(B*(k+y))/H :=
      div_le_div_of_nonneg_right (mul_le_mul hp hs (by positivity) (by positivity)) hH.le
    _ = (B^ε*B)*((k*y)^ε*(k+y)/H) := by ring
    _ = _ := by rw [←Real.rpow_add_one hB0.ne']
end OAI.CompletedGauss
