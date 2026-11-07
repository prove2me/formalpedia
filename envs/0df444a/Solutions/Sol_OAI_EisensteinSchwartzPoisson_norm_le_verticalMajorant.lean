-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.norm_le_verticalMajorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:57:37.087136+00:00
-- url     : https://prove2.me/submissions/41b2fef7-a941-4dcd-af35-2fbda485eec3

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open OAI.EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (f : SchwartzMap ℂ ℂ) (x y : ℝ) :
    ‖f (complexPoint x y)‖ ≤ verticalMajorant f y := by
  have h0 := SchwartzMap.norm_le_seminorm ℝ f (complexPoint x y)
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ f 2 (complexPoint x y)
  have hy : y ^ 2 ≤ ‖complexPoint x y‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, complexPoint]
    nlinarith [sq_nonneg x]
  have hym := mul_le_mul_of_nonneg_right hy (norm_nonneg (f (complexPoint x y)))
  have hden : 0 < 1 + y ^ 2 := by positivity
  rw [verticalMajorant, ← div_eq_mul_inv]
  apply (le_div_iff₀ hden).mpr
  nlinarith
end OAI.EisensteinSchwartzPoisson
