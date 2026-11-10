-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalSecondLiteralTerm_twisted_profiles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:28:56.357199+00:00
-- url     : https://prove2.me/submissions/cf955cd0-3e9a-4c60-97a7-852a17840814

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactProfiles
import Theorems.Thm_OAI_SecondPassIntegration_full_uniform_twisted_normalized_child_tests
import Theorems.Thm_OAI_SecondPassArithmetic_globalResidualScale_eq
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_ne_zero
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_ConcretePrimeRowBridge_span_idealGenerator
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
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_JointLogSeparation_halfNormalization_twist
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_globalActualResidualScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstColumnScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledColumnScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooled_log_coordinates
import Theorems.Thm_OAI_SecondPassArithmetic_secondMaskQuotient_span
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassArithmetic_weighted_secondRayChild_normalized
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
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)
open JointLogSeparation (halfNormalizationCLM frequencyTwist frequencyTwist_apply halfNormalization_twist)
open SecondPassFiber (newRow)
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU₁ : ∀ t,g₁ t ≠ 0 → U t=1) (hU₂ : ∀ t,g₂ t ≠ 0 → U t=1)
    (hg₁ : ∀ t,g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t,g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t| ≤ A+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
        [∀ i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i,lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀ i,lambda^2 ∣ p i-1)
        (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (θ₁ θ₂ ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι),
        0 < ell → x.source.divisor ⊆ x.source.sourceCommon → x.source.frequency ≠ 0 →
        let j := globalScaleIndex p side x
        globalSecondLiteralTerm p hp hcop hg F Ψ m ray (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell Y side x =
          globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x *
          postCommonSmoothPair p hp hcop hg (globalSecondRawPool F x)
            (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (globalSecondRawMask p m x)
            (globalSecondLabel p x) (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
            (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows (globalBinZ p ell side j x) (globalBinUd p j x)
            (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)
            (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j) := by
  have h1 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₁ A hg₁
  have h2 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := SecondPassIntegration.full_uniform_twisted_normalized_child_tests
    (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A 6 hA (by norm_num) h1 h2
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr F Ψ m ray θ₁ θ₂ ell Y side x hell hE hk
  dsimp only
  let j := globalScaleIndex p side x
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.source.divisor
  let m' := m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  have hX : 0 < X := div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (FirstPassCubeLabels.primeProductNorm_pos p hp _)
  have hr : Ideal.span {secondMaskQuotient p x.source.divisor x.source.sourceCommon hE}=Ideal.span {r} := by
    rw [secondMaskQuotient_span]
    exact (ConcretePrimeRowBridge.span_idealGenerator _).symm
  have htw₁ : ∀ t, frequencyTwist g₁ θ₁ t ≠ 0 → U t = 1 := by
    intro t ht
    apply hU₁ t
    intro hz
    exact ht (by simp [frequencyTwist_apply,hz])
  have htw₂ : ∀ t, frequencyTwist g₂ θ₂ t ≠ 0 → U t = 1 := by
    intro t ht
    apply hU₂ t
    intro hz
    exact ht (by simp [frequencyTwist_apply,hz])
  have hnorm := weighted_secondRayChild_normalized p hp hcop hg hinj hpr
    x.source.sourceCommon x.source.divisor hE (globalSecondRawPool F x) x.source.overlap Ψ Ψ
    m' c d x.source.frequency r ray hr X Y hX U hUc hUs (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W htw₁ htw₂
  have hscale : X/(‖ConcreteTraceCRT.eisEmbedding e‖^2*‖ConcreteTraceCRT.eisEmbedding r‖^2)=
      globalActualResidualScale p ell side x := globalResidualScale_eq p ell side x
  dsimp only at hnorm
  rw [hscale,halfNormalization_twist U hUc hUs,halfNormalization_twist U hUc hUs] at hnorm
  have hcoords := globalPooled_log_coordinates p hp ell hell side x hk
  have hid' := hid p hp hcop hg θ₁ θ₂ (globalLogRep j 5) (globalLogRep j 6) (globalLogRep j 7)
    (globalActualResidualScale p ell side x) (globalPooledColumnScale ell j) (globalLogRep j 8) Y
    (globalLogRep_pos j 5) (globalLogRep_pos j 6) (globalLogRep_pos j 7)
    (globalActualResidualScale_pos p hp ell hell side x) (globalPooledColumnScale_pos ell hell j) (globalLogRep_pos j 8)
    (globalSecondRawPool F x) x.source.overlap (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    m' r c d e x.source.frequency (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _) hk
    hcoords.1 hcoords.2.1 hcoords.2.2.1 hcoords.2.2.2.1 hcoords.2.2.2.2
  rw [hid'] at hnorm
  have hgoal := congrArg (fun z : ℂ => (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    ((Y : ℂ)*secondSourceCommonCoefficient p hg Ψ m' c d x.source.sourceCommon x.source.divisor) * z) hnorm
  have hrow : newRow (globalSecondTuple p x) = d*e*x.source.frequency := rfl
  have hlabel : globalSecondLabel p x = c*e*∏ i ∈ x.source.overlap,p i := rfl
  have hmask : globalSecondRawMask p m x = m'*r := rfl
  have hz : globalBinZ p ell side j x =
      Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j /
        globalActualResidualScale p ell side x) := rfl
  have hud : globalBinUd p j x = Real.log (SecondPassIntegration.elementNorm d/globalLogRep j 5) := rfl
  have hue : globalBinUe p j x = Real.log (SecondPassIntegration.elementNorm e/globalLogRep j 6) := rfl
  have huv : globalBinUv p j x = Real.log (primeProductNorm p x.source.overlap/globalLogRep j 7) := rfl
  have hkap : globalBinKap p j x = Real.log (SecondPassIntegration.elementNorm (d*e*x.source.frequency)/globalLogRep j 8) := rfl
  change globalSecondLiteralTerm p hp hcop hg F Ψ m ray (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell Y side x = _
  rw [hrow,hlabel,hmask,hz,hud,hue,huv,hkap]
  have hq := secondExpansionQuotient_of_subset p x.source hE
  simp only [globalSecondLiteralTerm,secondExpansionSource,Finset.sum_singleton,hq,
    globalSecondOuterWeight,secondNormalizedExpansionWeight,
    globalResidualScale_eq p ell side x,globalBinRadial,m',c,d,e,r,X,j,mul_neg,mul_assoc] at hgoal ⊢
  exact hgoal
end OAI.SecondPassArithmetic
