-- Prove2me | solution 1 for OAI.CubicReflectionKernel.mellinInv_euler_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:46:05.474135+00:00
-- url     : https://prove2.me/submissions/10a20b5f-33dd-4daf-8323-3a0839c81f57

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MainTermDifference
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_InverseContour
import Theorems.Thm_OAI_CubicReflectionKernel_inverseMellinIntegrand_differentiableAt
import Theorems.Thm_OAI_CubicReflectionKernel_inverseMellinIntegrand_vertical_integrable
import Theorems.Thm_OAI_CubicReflectionKernel_inverseMellinIntegrand_strip_bound
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_VerticalContourShift_integral_eq_of_strip_decay
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply



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
open OAI.CubicReflectionKernel
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace OAI.CubicReflectionKernel
theorem _root_.solution
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    mellinInv 0 (mellinEulerData V j) y = mellinInv σ (mellinEulerData V j) y := by
  obtain ⟨C, hC, hb⟩ := inverseMellinIntegrand_strip_bound V a b ha hsupp hV A j y hy
  have h0 : (0 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · norm_num
    · exact Nat.cast_nonneg A
  have hshift (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
      (∫ t : ℝ, inverseMellinIntegrand V j y ((-(1 / 4) : ℝ) + t * Complex.I)) =
      ∫ t : ℝ, inverseMellinIntegrand V j y ((ρ : ℂ) + t * Complex.I) := by
    apply VerticalContourShift.integral_eq_of_strip_decay
      (inverseMellinIntegrand V j y) (-(1 / 4)) ρ C hρ.1
    · intro z hzlo hzhi
      apply inverseMellinIntegrand_differentiableAt V a b ha hsupp hV j y hy z
      linarith
    · apply inverseMellinIntegrand_vertical_integrable V a b ha hsupp hV A j
        (-(1 / 4)) ⟨le_rfl, hρ.1.trans hρ.2⟩ y hy
    · exact inverseMellinIntegrand_vertical_integrable V a b ha hsupp hV A j ρ hρ y hy
    · intro r hr t
      exact hb r ⟨hr.1, hr.2.trans hρ.2⟩ t
  have heq := (hshift 0 h0).symm.trans (hshift σ hσ)
  simpa only [mellinInv, smul_eq_mul, inverseMellinIntegrand] using
    congrArg (fun z : ℂ => (1 / (2 * Real.pi) : ℝ) • z) heq
end OAI.CubicReflectionKernel
