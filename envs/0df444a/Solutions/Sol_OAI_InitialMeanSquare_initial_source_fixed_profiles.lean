-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_source_fixed_profiles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T09:32:03.981872+00:00
-- url     : https://prove2.me/submissions/892dc951-e56a-42ee-a5aa-0ad39ee680da

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceTransfer
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_ne_zero
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
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_secondMaskQuotient_spec
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassArithmetic_weighted_secondRayChild_normalized
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_OAI_SecondPassIntegration_elementNorm_pos
import Theorems.Thm_OAI_SecondPassIntegration_full_uniform_normalized_child_tests
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
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.append_first
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.first_append
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.source_append
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
open OAI.InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open JointLogSeparation (halfNormalizationCLM)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (elementNorm)
namespace OAI.InitialMeanSquare
theorem _root_.solution
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hU₁ : ∀t,g₁ t≠0→U t=1) (hU₂ : ∀t,g₂ t≠0→U t=1)
    (hg₁ : ∀t,g₁ t≠0→|t|≤A) (hg₂ : ∀t,g₂ t≠0→|t|≤A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7→ℝ→ℂ),
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0→|t|≤A+B+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀i,lambda^2∣p i-1)
        (F : Finset ι) (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex)
        (x : SecondExpansionData ι) (Z H E V₀ X₀ K : ℝ),
        x.divisor⊆x.sourceCommon → x.frequency≠0 →
        0<Z → 0<E → 0<V₀ → 0<X₀ → 0<K →
        let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
        let r := secondExpansionQuotient p x
        let X := residualScale p Z x
        let z := Real.log (primeProductNorm p x.overlap*X₀/X)
        let ue := Real.log (elementNorm e/E)
        let uv := Real.log (primeProductNorm p x.overlap/V₀)
        let kap := Real.log (elementNorm (e*x.frequency)/K)
        |z|≤B → |ue|≤B → |uv|≤B → |kap|≤B →
        secondExpansionSource p hp hcop hg F Ψ m 1 1 ray {x}
          (fun S => normalizedColumn p (fun T => g₁ (columnLog p Z T)) S)
          (fun S => normalizedColumn p (fun T => g₂ (columnLog p Z T)) S) W H =
        sourceWeight p hp hcop hg Ψ m ray Z H x *
          postCommonSmoothPair p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
            (m*r) (e*∏i∈x.overlap,p i) (e*x.frequency) (-(e*x.frequency))
            A₁ A₂ W windows z 0 ue uv kap X₀ X₀ (H*K/(E^2*V₀^2*X₀^2)) := by
  have h1 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₁ A hg₁
  have h2 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := SecondPassIntegration.full_uniform_normalized_child_tests
    (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A B hA hB h1 h2
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr F Ψ m ray x Z H E V₀ X₀ K hE hk hZ hEs hV hX₀ hK
  dsimp only
  intro hz hue huv hkap
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
  let r := secondExpansionQuotient p x
  have he : e≠0 := primeSubsetGenerator_ne_zero _ _
  have hq : secondMaskQuotient p x.divisor x.sourceCommon hE=r :=
    (secondExpansionQuotient_of_subset p x hE).symm
  have hr : r≠0 := by
    rw [←hq]
    intro hr0
    have hs := secondMaskQuotient_spec p x.divisor x.sourceCommon hE
    rw [hr0,mul_zero] at hs
    exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) hs
  have hX : 0<residualScale p Z x := div_pos hZ
    (mul_pos (SecondPassIntegration.elementNorm_pos e he) (SecondPassIntegration.elementNorm_pos r hr))
  have hnorm := weighted_secondRayChild_normalized p hp hcop hg hinj hpr
    x.sourceCommon x.divisor hE F x.overlap Ψ Ψ m 1 1 x.frequency r ray
      (congrArg (fun a:O => Ideal.span {a}) hq) Z H hZ U hUc hUs g₁ g₂ W hU₁ hU₂
  dsimp only at hnorm
  have hnormone : elementNorm (1:O)=1 := by simp [elementNorm]
  have hid' := hid p hp hcop hg 1 E V₀ (residualScale p Z x) X₀ K H
    (by norm_num) hEs hV hX hX₀ hK F x.overlap (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      m r 1 1 e x.frequency one_ne_zero he hk hz
      (by simpa only [hnormone,div_one,Real.log_one,abs_zero] using hB) hue huv
      (by simpa only [one_mul] using hkap)
  simp only [one_mul,mul_neg,hnormone,div_one,Real.log_one] at hid'
  have hscale : Z/(‖eisEmbedding e‖^2*‖eisEmbedding r‖^2)=residualScale p Z x := rfl
  rw [hscale,hid'] at hnorm
  rw [hq] at hnorm
  have hgoal := congrArg (fun t:ℂ => ((H:ℂ)*secondSourceCommonCoefficient p hg Ψ m 1 1 x.sourceCommon x.divisor)*t) hnorm
  simp only [secondExpansionSource,Finset.sum_singleton,sourceWeight,
    secondNormalizedExpansionWeight,e,r,mul_assoc] at hgoal ⊢
  exact hgoal
end OAI.InitialMeanSquare
