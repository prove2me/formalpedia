-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.norm_inverse_horizontalSlice_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:58:54.915213+00:00
-- url     : https://prove2.me/submissions/4bb688e4-4229-4efe-a0cb-c588ebfb9458

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_norm_horizontalSlice_le
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
theorem _root_.solution (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * Real.pi := by
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice F η)) x,
    Real.fourierInv_eq]
  have hb : Integrable (fun ξ : ℝ =>
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have h := norm_integral_le_of_norm_le
    (f := fun ξ : ℝ => Real.fourierChar (inner ℝ ξ x) • horizontalSlice F η ξ) hb (Eventually.of_forall fun ξ => by
    simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
      norm_horizontalSlice_le F η ξ)
  simpa only [integral_const_mul, integral_univ_inv_one_add_sq] using h
end OAI.EisensteinSchwartzPoisson
