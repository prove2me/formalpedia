-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.hasSieveExponent_of_threshold_band
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:24:13.29989+00:00
-- url     : https://prove2.me/submissions/28da7a49-05e5-4c3d-ae39-9629e1b2dd39

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonConstants
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Theorems.Thm_OAI_CanonicalQuadraticSieve_sieveNorm_large_rows
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_sieveNorm_mono
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_initialSieveConstant_pos
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.spatialTriple_one
attribute [local simp] OAI.CubicEisenstein.spatialTriple_two
attribute [local simp] OAI.CubicEisenstein.spatialTriple_zero
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.FirstPassCubeLabels.coreRayTwist_prod
attribute [local simp] OAI.FirstPassCubeLabels.twisted_core_product
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply



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
open scoped BigOperators Classical SchwartzMap
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise
open OAI.CanonicalQuadraticSieve
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (β : ℝ) (_hβ1 : 1≤β) (hβ2 : β≤2)
    (hband : ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M N : ℝ,
      1≤M → 1≤N → N^β≤M → M≤N^2 → sieveNorm M N≤C*(M*N)^ρ*M) :
    HasSieveExponent β := by
  intro ε hε
  have hρ : 0<ε/3 := by positivity
  obtain ⟨C,hC,hbound⟩ := hband (ε/3) hρ
  let I := QuadraticInitialBound.initialSieveConstant
  have hI : 0<I := QuadraticInitialBound.initialSieveConstant_pos
  refine ⟨C+5*I,by positivity,?_⟩
  intro M N hM hN
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hMN : 1≤M*N := by nlinarith
  have hpow : 1≤(M*N)^ε := Real.one_le_rpow hMN hε.le
  have hNb : 0≤N^β := Real.rpow_nonneg hN0.le _
  by_cases hlarge : N^2≤M
  · calc
      _ ≤ 5*I*M := sieveNorm_large_rows M N hM hN hlarge
      _ = (5*I)*1*M := by ring
      _ ≤ (C+5*I)*(M*N)^ε*(M+N^β) := by gcongr <;> linarith
  · let R := max M (N^β)
    have hNβsq : N^β≤N^2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hN hβ2
    have hR : 1≤R := hM.trans (le_max_left _ _)
    have hRM : M≤R := le_max_left _ _
    have hRN : N^β≤R := le_max_right _ _
    have hRsq : R≤N^2 := max_le (le_of_not_ge hlarge) hNβsq
    have hb := hbound R N hR hN hRN hRsq
    have hmono := sieveNorm_mono hRM (le_refl N)
    have hN2 : 1≤N^2 := one_le_pow₀ hN
    have hM3 : M≤M^3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hM (show (1:ℕ)≤3 by decide)
    have hRN2 : R≤M*N^2 := by
      apply max_le
      · nlinarith
      · exact hNβsq.trans (by nlinarith)
    have hprod : R*N≤(M*N)^3 := by
      calc
        _ ≤ (M*N^2)*N := mul_le_mul_of_nonneg_right hRN2 hN0.le
        _ = M*N^3 := by ring
        _ ≤ M^3*N^3 := mul_le_mul_of_nonneg_right hM3 (by positivity)
        _ = _ := by ring
    have hRprod : (R*N)^(ε/3)≤(M*N)^ε := by
      calc
        _ ≤ ((M*N)^3)^(ε/3) := Real.rpow_le_rpow (by positivity) hprod hρ.le
        _ = _ := by
          rw [←Real.rpow_natCast (M*N) 3,←Real.rpow_mul (by positivity : 0≤M*N)]
          congr 1
          ring
    have hRadd : R≤M+N^β := max_le (by linarith) (by linarith)
    exact hmono.trans (hb.trans (by gcongr ; linarith))
end OAI.CanonicalQuadraticSieve
