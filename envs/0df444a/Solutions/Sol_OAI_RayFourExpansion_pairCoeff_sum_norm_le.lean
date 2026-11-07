-- Prove2me | solution 1 for OAI.RayFourExpansion.pairCoeff_sum_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:29:58.142888+00:00
-- url     : https://prove2.me/submissions/f034db14-d06b-44e1-a55b-12dcc33e4f04

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
import Theorems.Thm_OAI_FiniteRayExpansion_unitTensorCoeff_sum_norm_le
import Theorems.Thm_OAI_RayFourExpansion_rayUnit_card_le

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
theorem _root_.solution (f : RayRing → RayRing → ℂ) (B : ℝ)
    (hf : ∀ u v : RayRingˣ, ‖f (u : RayRing) (v : RayRing)‖ ≤ B) :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖pairCoeff f χ η‖) ≤ 256 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 1 1)
  have hcard : (Fintype.card RayRingˣ : ℝ) ^ 2 ≤ 256 := by
    have h : (Fintype.card RayRingˣ : ℝ) ≤ 16 := by exact_mod_cast rayUnit_card_le
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card RayRingˣ)]
  exact (unitTensorCoeff_sum_norm_le _ B hf).trans (mul_le_mul_of_nonneg_right hcard hB)
end OAI.RayFourExpansion
