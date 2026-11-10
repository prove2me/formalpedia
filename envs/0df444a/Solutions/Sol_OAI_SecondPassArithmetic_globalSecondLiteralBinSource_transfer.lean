-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalSecondLiteralBinSource_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:23:01.231089+00:00
-- url     : https://prove2.me/submissions/3217dae5-965c-4e3c-908a-540143942409

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
import Theorems.Thm_OAI_SecondPassArithmetic_sum_globalArithmeticBin
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
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
import Theorems.Thm_OAI_FourierBridge_exists_complex_smooth_cutoff
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondLiteralTerm_twisted_profiles
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassArithmetic_weightedGlobalPositiveBin_transfer
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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open JointLogSeparation (frequencyTwist)
open SecondPassIntegration (densityChildEnergy)
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (ε : ℝ) (hε : 0 < ε) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (M : ℝ) (hM : 0 ≤ M)
    (hg₁ : ∀ t,g₁ t ≠ 0 → |t| ≤ M) (hg₂ : ∀ t,g₂ t ≠ 0 → |t| ≤ M)
    (A J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C : ℝ),0 ≤ C ∧
      (∀ i,HasCompactSupport (windows i)) ∧
      (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t| ≤ M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (θ₁ θ₂ K ell B F : ℝ) (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
      (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (γ : GlobalSecondData ι → ℂ) (Γ : ℝ),
      0 < K → 0 < ell → 0 < B → 0 < F → 0 ≤ Γ → (∀ x∈s,‖γ x‖ ≤ Γ) → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      globalBinFirstCoefficient K ell B F j *
      ‖globalSecondLiteralBinSource p hp hcop hg γ s side j pool Ψ m
        (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell (globalPooledRowScale K ell B F j)‖ ≤
      ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight (Γ*C) ε θ₁ θ₂ K ell B F A J j ray q *
        (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (windows 5) (windows 6)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J /
          (globalPooledColumnScale ell j*globalPooledLabelScale j)) := by
  obtain ⟨U,hUc,hUs,hUone,hUsupp,hUzero⟩ := FourierBridge.exists_complex_smooth_cutoff M hM
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := globalSecondLiteralTerm_twisted_profiles U hUc hUs
    g₁ g₂ W M hM (fun t ht => hUone t (hg₁ t ht)) (fun t ht => hUone t (hg₂ t ht)) hg₁ hg₂
  obtain ⟨C,hC,htrans⟩ := weightedGlobalPositiveBin_transfer ε hε A₁ A₂ W windows
    (fun _ => M+6+1) (fun _ => by linarith) hwb hwc (fun i => (hws i).continuous) A J
  refine ⟨windows,C,hC,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr θ₁ θ₂ K ell B F s side j pool Ψ m γ Γ hK hell hB hF hΓ hγ hΨ hs hk
  have heq : globalSecondLiteralBinSource p hp hcop hg γ s side j pool Ψ m
      (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell (globalPooledRowScale K ell B F j) =
      ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j pool Ψ m ray
          (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows ell (globalPooledRowScale K ell B F j) := by
    unfold globalSecondLiteralBinSource
    apply Finset.sum_congr rfl
    intro ray hray
    rw [sum_globalArithmeticBin p s side j]
    apply Finset.sum_congr rfl
    intro q hq
    unfold weightedGlobalArithmeticBinSource globalSecondRawSource
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨hxs,hxq,hxj⟩ := Finset.mem_filter.mp hx
    have h := hid p hp hcop hg hinj hpr pool Ψ m ray θ₁ θ₂ ell
      (globalPooledRowScale K ell B F j) side x hell (hs x hxs).2.1 (hk x hxs)
    dsimp only at h
    rw [hxj] at h
    rw [h,mul_assoc]
  rw [heq]
  simpa only [globalDescentWeight,norm_neg] using
    htrans p hp hcop hg hinj hc (-θ₁) θ₂ K ell B F s side j pool Ψ m γ Γ
      hK hell hB hF hΓ hγ hΨ hs hk
end OAI.SecondPassArithmetic
