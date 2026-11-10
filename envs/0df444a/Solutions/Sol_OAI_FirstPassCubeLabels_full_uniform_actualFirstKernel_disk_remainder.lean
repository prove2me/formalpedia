-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.full_uniform_actualFirstKernel_disk_remainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:10:33.799734+00:00
-- url     : https://prove2.me/submissions/bf8c1693-9577-427e-a1fe-f47aff0ebc81

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceRemainders
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DualZeroMode
import Theorems.Thm_OAI_FirstPassCubeLabels_actualFirstKernel_complement_eq_pairs
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
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
import Theorems.Thm_OAI_FirstPassCubeLabels_full_uniform_canonicalPairMode_disk_remainder
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_union
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_apply
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
import Theorems.Thm_OAI_SecondPassArithmetic_columnLog_norm_upper
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_apply
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_source
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.kernelLocalLift_symm
attribute [local simp] OAI.CubicEisenstein.kernelQuotientChart_symm
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
attribute [local simp] OAI.InitialMeanSquare.initialLogProfile_apply
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
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply



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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open SecondPassArithmetic (boundedPrimeSupports boundedPrimeSupports_card_positive
  columnLog_norm_upper firstFrequencyDisk primeProductNorm_ge_one)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),Disjoint F B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ X₁ X₂ K P M₁ M₂ : ℝ),
      0≤G₁ → 0≤G₂ → 0<X₁ → 0<X₂ → 0<K → 0≤P →
      (∀N∈F.powerset,‖C₁ N‖≤G₁) → (∀N∈F.powerset,‖C₂ N‖≤G₂) →
      (∀N∈F.powerset,C₁ N≠0 → columnLog p X₁ N≤M₁) →
      (∀N∈F.powerset,C₂ N≠0 → columnLog p X₂ N≤M₂) →
      ∀(d : O),d≠0 →
      let U₁ := X₁*Real.exp M₁
      let U₂ := X₂*Real.exp M₂
      let slow := K/(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*U₁*U₂)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val‖≤
      (128*U₁)*(128*U₂)*(G₁*G₂*K)*
        ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_disk_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc F B v ε₁ ε₂ hFB C₁ C₂ W G₁ G₂ X₁ X₂ K P M₁ M₂ hG₁ hG₂ hX₁ hX₂ hK hP hC₁ hC₂ hS₁ hS₂ d hd
  dsimp only
  let U₁:=X₁*Real.exp M₁
  let U₂:=X₂*Real.exp M₂
  let S:=cubeActiveSupport B v ε₁ ε₂
  let T:=firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
  let slow:=K/(‖eisEmbedding d‖^2*primeProductNorm p S*U₁*U₂)
  let tail:ℝ:=(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^A)
  let Q:ℝ:=G₁*G₂*K*tail
  have hU₁:0<U₁:=mul_pos hX₁ (Real.exp_pos _)
  have hU₂:0<U₂:=mul_pos hX₂ (Real.exp_pos _)
  have hNd:0<‖eisEmbedding d‖^2:=sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hslow:0<slow:=div_pos hK (mul_pos (mul_pos (mul_pos hNd (primeProductNorm_pos p hp S)) hU₁) hU₂)
  have hH:0≤P/Real.exp (M₁+M₂):=div_nonneg hP (Real.exp_pos _).le
  have htail:0≤tail:=by dsimp [tail]; positivity
  have hQ:0≤Q:=mul_nonneg (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le) htail
  let rem (N R:Finset ι):ℂ:=if Disjoint N R then
    ∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N R B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val else 0
  have hnzero (N R:Finset ι) (hn:C₁ N=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hn]
  have hrzero (N R:Finset ι) (hr:C₂ R=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hr]
  have heq : (∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val)=
      ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,rem N R := by
    rw [actualFirstKernel_complement_eq_pairs p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K hK d hd T]
    change (∑N∈F.powerset,∑R∈F.powerset,rem N R)=_
    calc
      _ = ∑N∈boundedPrimeSupports p F U₁,∑R∈F.powerset,rem N R := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro N hN hn
        have hz:C₁ N=0:=by
          by_contra h
          exact hn (Finset.mem_filter.mpr ⟨hN,columnLog_norm_upper p hp X₁ M₁ hX₁ N (hS₁ N hN h)⟩)
        simp only [hnzero N _ hz,Finset.sum_const_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro N hN
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro R hR hr
        have hz:C₂ R=0:=by
          by_contra h
          exact hr (Finset.mem_filter.mpr ⟨hR,columnLog_norm_upper p hp X₂ M₂ hX₂ R (hS₂ R hR h)⟩)
        exact hrzero N R hz
  have hrem (N:Finset ι) (hN:N∈boundedPrimeSupports p F U₁) (R:Finset ι) (hR:R∈boundedPrimeSupports p F U₂):‖rem N R‖≤Q:=by
    have hNF: N∈F.powerset:=(Finset.mem_filter.mp hN).1
    have hRF: R∈F.powerset:=(Finset.mem_filter.mp hR).1
    by_cases hn:C₁ N=0
    · rw [hnzero N R hn,norm_zero]; exact hQ
    by_cases hr:C₂ R=0
    · rw [hrzero N R hr,norm_zero]; exact hQ
    by_cases hNR:Disjoint N R
    · have hNB:=hFB.mono_left (Finset.mem_powerset.mp hNF)
      have hRB:=hFB.mono_left (Finset.mem_powerset.mp hRF)
      have hNS:Disjoint N S:=hNB.mono_right (Finset.filter_subset _ _)
      have hRS:Disjoint R S:=hRB.mono_right (Finset.filter_subset _ _)
      have hnorm:primeProductNorm p ((N∪R)∪S)=primeProductNorm p N*primeProductNorm p R*primeProductNorm p S:=by
        rw [primeProductNorm_union p _ _ (Finset.disjoint_union_left.mpr ⟨hNS,hRS⟩),primeProductNorm_union p _ _ hNR]
      have hprod:=mul_le_mul (Finset.mem_filter.mp hN).2 (Finset.mem_filter.mp hR).2
        (primeProductNorm_pos p hp R).le hU₁.le
      have hscale:slow≤K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S)):=by
        apply div_le_div_of_nonneg_left hK.le (mul_pos hNd (primeProductNorm_pos p hp _))
        rw [hnorm]
        calc
          _ ≤ ‖eisEmbedding d‖^2*(U₁*U₂*primeProductNorm p S):=mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
          _ = _ := by ring
      have hnroot:1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖:=by
        have hx:=primeProductNorm_ge_one p hp ((N∪R)∪S)
        change 1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖^2 at hx
        nlinarith [norm_nonneg (eisEmbedding (∏i∈(N∪R)∪S,p i))]
      have hpre:(K/‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖)*(‖C₁ N‖*‖C₂ R‖)≤G₁*G₂*K:=by
        calc
          _ ≤ K*(G₁*G₂):=mul_le_mul (div_le_self hK.le hnroot)
            (mul_le_mul (hC₁ N hNF) (hC₂ R hRF) (norm_nonneg _) hG₁)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK.le
          _ = _ := by ring
      have hfrac:(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S))))^2*(1+P/Real.exp (M₁+M₂))^A)≤tail:=by
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos (sq_pos_of_pos (lt_min (by norm_num) hslow)) (pow_pos (by linarith) _))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_min zero_le_one hslow.le)
          (min_le_min_left 1 hscale) 2) (pow_nonneg (by linarith) _)
      have hpair:=hb p hp hcop hg hc N R B v ε₁ ε₂ hNR hNB hRB C₁ C₂ W (fun _=>1) (fun _=>1)
        X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hP (hS₁ N hNF hn) (hS₂ R hRF hr) d hd
      simp only [norm_one,one_mul] at hpair
      dsimp only [rem]
      rw [if_pos hNR]
      exact hpair.trans (mul_le_mul hpre hfrac (by positivity) (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le))
    · simp only [rem,if_neg hNR,norm_zero];exact hQ
  rw [heq]
  calc
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,‖rem N R‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun N hN=>norm_sum_le _ _))
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,Q:=
      Finset.sum_le_sum (fun N hN=>Finset.sum_le_sum (fun R hR=>hrem N hN R hR))
    _ = ((boundedPrimeSupports p F U₁).card:ℝ)*((boundedPrimeSupports p F U₂).card:ℝ)*Q:=by simp;ring
    _ ≤ (128*U₁)*(128*U₂)*Q:=mul_le_mul_of_nonneg_right
      (mul_le_mul (boundedPrimeSupports_card_positive p hp hinj F U₁ hU₁)
        (boundedPrimeSupports_card_positive p hp hinj F U₂ hU₂) (Nat.cast_nonneg _) (by positivity)) hQ
    _ = _ := by dsimp [Q,tail,slow,U₁,U₂,S];ring
end OAI.FirstPassCubeLabels
