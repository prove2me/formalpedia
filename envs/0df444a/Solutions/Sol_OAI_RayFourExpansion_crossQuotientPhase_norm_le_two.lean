-- Prove2me | solution 1 for OAI.RayFourExpansion.crossQuotientPhase_norm_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:23:28.881588+00:00
-- url     : https://prove2.me/submissions/79cdad5e-7901-4e9d-94e7-c8279ba87104

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
import Theorems.Thm_OAI_RayFourExpansion_quadraticRayValue_bounds

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
open scoped BigOperators Classical
open OAI.RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT ActualEisensteinCoordinates QuadraticGaussRay
open FiniteRayExpansion
namespace OAI.RayFourExpansion
theorem _root_.solution (r s : RayRing) : ‖crossQuotientPhase r s‖ ≤ 2 := by
  unfold crossQuotientPhase MixedCrossSeparation.quadraticRayPair
  rw [div_eq_mul_inv, mul_inv_rev, norm_mul, norm_mul]
  calc
    _ ≤ 2 * (1 * 1) :=
      mul_le_mul (quadraticRayValue_bounds _).1
        (mul_le_mul (quadraticRayValue_bounds _).2 (quadraticRayValue_bounds _).2
          (norm_nonneg _) (by norm_num))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = 2 := by norm_num
end OAI.RayFourExpansion
