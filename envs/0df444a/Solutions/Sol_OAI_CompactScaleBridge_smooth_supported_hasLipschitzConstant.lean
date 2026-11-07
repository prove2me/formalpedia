-- Prove2me | solution 1 for OAI.CompactScaleBridge.smooth_supported_hasLipschitzConstant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:43:12.4332+00:00
-- url     : https://prove2.me/submissions/c64628dd-19f8-452e-9012-bc3de94ae7fc

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
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
open OAI.CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge
namespace OAI.CompactScaleBridge
theorem _root_.solution
    (W : ℝ → ℂ) (hSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hSupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0) :
    ∃ LipC : ℝ, 0 ≤ LipC ∧
      ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y| := by
  have hCompact : HasCompactSupport W := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro x hx
    constructor
    · by_contra h
      have hxle : x ≤ 1 := le_of_not_ge h
      exact hx (hSupp x (Or.inl hxle))
    · by_contra h
      have hxge : 2 ≤ x := le_of_not_ge h
      exact hx (hSupp x (Or.inr hxge))
  obtain ⟨C, hC⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hCompact hSmooth (by simp)
  refine ⟨(C : ℝ), C.2, ?_⟩
  intro x y
  simpa only [dist_eq_norm, Real.norm_eq_abs] using hC.dist_le_mul x y
end OAI.CompactScaleBridge
