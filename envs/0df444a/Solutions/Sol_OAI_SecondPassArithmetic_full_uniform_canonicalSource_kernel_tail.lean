-- Prove2me | solution 1 for OAI.SecondPassArithmetic.full_uniform_canonicalSource_kernel_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:15:13.819446+00:00
-- url     : https://prove2.me/submissions/138fd337-7e83-4abe-a2b1-a75de3d41fb2

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceRemainders
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DualZeroMode
import Theorems.Thm_OAI_FirstPassCubeLabels_full_uniform_actualFirstKernel_disk_remainder
import Theorems.Thm_OAI_SecondPassArithmetic_originalLabelColumn_core_norm_le
import Theorems.Thm_OAI_SecondPassArithmetic_originalLabelColumn_core_test_ne_zero
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalFirstFrequencyRadius_eq_global
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_ne_zero
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
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
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
import Theorems.Thm_OAI_SecondPassArithmetic_canonical_log_kernel
import Theorems.Thm_OAI_SecondPassArithmetic_primeSubsetGenerator_norm_eq_productNorm
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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.SecondPassArithmetic
theorem _root_.solution (A : ℕ) :
    ∃(s:Finset (ℕ×ℕ)) (Ctail:ℝ),0<Ctail ∧
    ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (b:CubeCoordinates ι),b.Admissible → ∀ C D:Finset ι,Disjoint C b.support →
      ∀(Ψ₁ Ψ₂:O→*ℂ),(∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      ∀(m₁ m₂ f:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (G₁ G₂ M₁ M₂ Ksrc K ell:ℝ),
      0≤G₁ → 0≤G₂ → 0<Ksrc → 0<K → 0<ell →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) →
      (∀t,g₁ t≠0→t≤M₁) → (∀t,g₂ t≠0→t≤M₂) →
      let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
      let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
      let U₁:=X₁*Real.exp M₁
      let U₂:=X₂*Real.exp M₂
      let slow:=Ksrc/(primeProductNorm p D*primeProductNorm p
        (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)*U₁*U₂)
      let T:=firstFrequencyDisk (globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D))
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun S=>g₁ (columnLog p ell S)))
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f (fun S=>g₂ (columnLog p ell S)))
        W (fun _=>1) (fun _=>1) 1 1 Ksrc
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val‖≤
      (128*U₁)*(128*U₂)*(G₁*G₂*Ksrc)*
        ((Ctail*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+(Ksrc/K)/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,Ctail,hCtail,hbound⟩:=full_uniform_actualFirstKernel_disk_remainder A
  refine ⟨s,Ctail,hCtail,?_⟩
  intro ι _ p hp _ hinj hcop hg hc pool b hb C D hCB Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f g₁ g₂ W G₁ G₂ M₁ M₂ Ksrc K ell hG₁ hG₂ hKsrc hK hell hg₁ hg₂ hM₁ hM₂
  dsimp only
  let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
  let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
  have hX₁:0<X₁:=div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
  have hX₂:0<X₂:=div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
  have hFB:Disjoint (pool\(b.support∪C)) b.support:=Finset.disjoint_left.mpr (fun i hi hb=>
    (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hb))
  let C₁:=originalLabelColumn p hg b.support b.leftBit b.rightBit true
    (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) (∏i∈C,p i) f
  let C₂:=originalLabelColumn p hg b.support b.leftBit b.rightBit false
    (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) (∏i∈C,p i) f
  have hcoef₁ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset):‖C₁ N‖≤G₁:=
    (originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit true Ψ₁ hΨ₁ m₁ _ f _ N).trans (hg₁ _)
  have hcoef₂ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset):‖C₂ N‖≤G₂:=
    (originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit false Ψ₂ hΨ₂ m₂ _ f _ N).trans (hg₂ _)
  have hs₁ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset) (hn:C₁ N≠0):columnLog p X₁ N≤M₁:=
    hM₁ _ (originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit true Ψ₁ m₁ _ f _ N hn)
  have hs₂ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset) (hn:C₂ N≠0):columnLog p X₂ N≤M₂:=
    hM₂ _ (originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit false Ψ₂ m₂ _ f _ N hn)
  have h:=hbound p hp hinj hcop hg hc (pool\(b.support∪C)) b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit hFB C₁ C₂ W
    G₁ G₂ X₁ X₂ Ksrc (Ksrc/K) M₁ M₂ hG₁ hG₂ hX₁ hX₂ hKsrc (div_pos hKsrc hK).le
    hcoef₁ hcoef₂ hs₁ hs₂ (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) (primeSubsetGenerator_ne_zero _ _)
  rw [canonicalFirstFrequencyRadius_eq_global p hp b hb C D Ksrc K ell hKsrc hK] at h
  simp only [primeSubsetGenerator_norm_eq_productNorm] at h
  have heq := fun h:O=>canonical_log_kernel p hp hcop hg pool b hb C hCB Ψ₁ Ψ₂ m₁ m₂ f
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h g₁ g₂ W Ksrc ell hell
  simp_rw [heq]
  exact h
end OAI.SecondPassArithmetic
