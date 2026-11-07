-- Prove2me | solution 1 for OAI.CubicReflectionKernel.reflectedLogProfile_source_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:46:59.6796+00:00
-- url     : https://prove2.me/submissions/ae43d633-4ea0-426a-89f4-4aa33c628913

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ReflectedKernel
import Theorems.Thm_OAI_CubicReflectionKernel_reflectedLogProfile_deriv_bound
import Theorems.Thm_OAI_CubicReflectionKernel_momentScale_nonneg
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_schwartzCLM_finite_seminorm_control
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FourierBridge_fourier_coefficient_moment
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
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
open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory
namespace OAI.CubicReflectionKernel
theorem _root_.solution (j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (logSource : SchwartzMap ℝ ℂ) (y : ℝ),
        ‖iteratedDeriv j (reflectedLogProfile logSource) y‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by
  let m := j + (volume : Measure ℝ).integrablePower
  let S : Finset (ℕ × ℕ) := {(0, 0), (m, 0)}
  obtain ⟨s, C, hC, hbound⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control (E := ℝ)
    (FourierTransform.fourierCLM ℝ (SchwartzMap ℝ ℂ)) S
  refine ⟨s, (2 * Real.pi) ^ j * (momentScale + 1) * (2 * C), by
    have := momentScale_nonneg
    positivity, ?_⟩
  intro logSource y
  have h0' : schwartzSeminormFamily ℝ ℝ ℂ (0, 0) ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
    Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S])
  have hm' : schwartzSeminormFamily ℝ ℝ ℂ (m, 0) ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
    Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S])
  have h0 := Seminorm.le_def.mp h0' (𝓕 logSource)
  have hm := Seminorm.le_def.mp hm' (𝓕 logSource)
  change SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) ≤ _ at h0
  change SchwartzMap.seminorm ℝ m 0 (𝓕 logSource) ≤ _ at hm
  have hs := hbound logSource
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (𝓕 logSource) ≤ _ at hs
  have hsum : SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) + SchwartzMap.seminorm ℝ m 0 (𝓕 logSource) ≤
      2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by linarith
  have hmoment := FourierBridge.fourier_coefficient_moment logSource j
  change (∫ u : ℝ, ‖u‖ ^ j * ‖(𝓕 logSource) u‖) ≤ momentScale *
    (SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) + SchwartzMap.seminorm ℝ m 0 (𝓕 logSource)) at hmoment
  calc
    _ ≤ (2 * Real.pi) ^ j * ∫ u : ℝ, ‖u‖ ^ j * ‖(𝓕 logSource) u‖ :=
      reflectedLogProfile_deriv_bound logSource j y
    _ ≤ (2 * Real.pi) ^ j * (momentScale *
        (2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource)) := by
      exact mul_le_mul_of_nonneg_left
        (hmoment.trans (mul_le_mul_of_nonneg_left hsum momentScale_nonneg)) (by positivity)
    _ ≤ _ := by
      have hpos : 0 ≤ 2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by positivity
      calc
        _ ≤ (2 * Real.pi) ^ j * ((momentScale + 1) *
            (2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right zero_le_one) hpos) (by positivity)
        _ = _ := by ring
end OAI.CubicReflectionKernel
