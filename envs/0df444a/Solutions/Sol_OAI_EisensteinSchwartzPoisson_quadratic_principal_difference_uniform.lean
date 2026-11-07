-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.quadratic_principal_difference_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:48:19.162402+00:00
-- url     : https://prove2.me/submissions/c8950deb-a512-4839-83b0-56ed642188d1

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_KernelEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_two_profile_seminorm_control
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_maskedPrincipalRemainder_uniform
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_ActualEisensteinCubic_quadratic_square_poisson_main_cancel
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
import Theorems.Thm_OAI_QuadraticInitialBound_pvConstant_pos
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
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
open scoped BigOperators Classical SchwartzMap FourierTransform
open OAI.EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT
open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
          (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s, C, hC, hb⟩ := two_profile_seminorm_control
    quadraticTransformedSquareProfileCLM quadraticSquareProfileCLM pvSeminorms
  refine ⟨s, pvConstant * C, mul_pos pvConstant_pos hC, ?_⟩
  intro α _ P _ hinj S W M hM
  have hbound := hb W
  simp only [quadraticTransformedSquareProfileCLM_apply, quadraticSquareProfileCLM_apply] at hbound
  rw [quadratic_square_poisson_main_cancel P hinj S W M hM]
  calc
    _ ≤ ‖maskedPrincipalRemainder P S (quadraticTransformedSquareProfile W) M‖ +
        ‖maskedPrincipalRemainder P S (quadraticSquareProfile W) M‖ := norm_sub_le _ _
    _ ≤ (2 : ℝ) ^ S.card * pvControl (quadraticTransformedSquareProfile W) +
        (2 : ℝ) ^ S.card * pvControl (quadraticSquareProfile W) :=
      add_le_add (maskedPrincipalRemainder_uniform P S _ M hM) (maskedPrincipalRemainder_uniform P S _ M hM)
    _ = (2 : ℝ) ^ S.card * pvConstant *
        (pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W) +
          pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) := by unfold pvControl; ring
    _ ≤ (2 : ℝ) ^ S.card * pvConstant * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
      exact mul_le_mul_of_nonneg_left hbound (mul_nonneg (by positivity) pvConstant_pos.le)
    _ = _ := by ring
end OAI.EisensteinSchwartzPoisson
