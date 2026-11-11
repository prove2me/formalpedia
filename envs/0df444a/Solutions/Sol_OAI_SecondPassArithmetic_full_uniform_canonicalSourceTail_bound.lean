-- Prove2me | solution 1 for OAI.SecondPassArithmetic.full_uniform_canonicalSourceTail_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:54:00.998286+00:00
-- url     : https://prove2.me/submissions/7a97d55c-f0e6-4465-a299-97860eea42e8

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_RetainedDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalTailBounds
import Theorems.Thm_OAI_SecondPassArithmetic_firstTail_scalar_bound
import Theorems.Thm_OAI_SecondPassArithmetic_cubeCoordinates_radical_bound
import Theorems.Thm_OAI_SecondPassArithmetic_cubeSourceDivisor_norm_bound
import Theorems.Thm_OAI_SecondPassArithmetic_cubeSourceDivisors_card
import Theorems.Thm_OAI_SecondPassArithmetic_sourceMobiusDivisor_norm_le_one
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalCubeDualTail_support
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
import Theorems.Thm_OAI_DescentFiberCost_finite_ideal_count_real
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
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalCubeOuter_norm_le_one
import Theorems.Thm_OAI_SecondPassArithmetic_cube_coordinates_parity_count
import Theorems.Thm_OAI_SecondPassArithmetic_full_uniform_canonicalSource_kernel_tail
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_mono
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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.SecondPassArithmetic
theorem _root_.solution (ε:ℝ) (hε:0<ε) (A:ℕ):
    ∃(s:Finset (ℕ×ℕ)) (C:ℝ),0<C ∧
    ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal ActualEisensteinCubic.O))
      (a:CubeCoordinates ι→Finset ι→Ideal ActualEisensteinCubic.O→ℂ) (Ψ₁ Ψ₂:ActualEisensteinCubic.O→*ℂ)
      (m₁ m₂:ActualEisensteinCubic.O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ M₁ M₂ Ksrc K ell B F lengthScale:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<Ksrc → 0<K → 0<ell → 1≤B → 1≤F → 1≤lengthScale →
      ell*Real.exp M₁≤lengthScale → ell*Real.exp M₂≤lengthScale →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖a b D I‖≤Γ) →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) →
      (∀t,g₁ t≠0→t≤M₁) → (∀t,g₂ t≠0→t≤M₂) →
      ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell‖≤
      C*B^(4+ε)*lengthScale^4*F*Γ*(G₁*G₂*Ksrc)*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*
        (1+lengthScale^3*B^4/Ksrc)^2/(1+(Ksrc/K)/Real.exp (M₁+M₂))^A := by
  obtain ⟨s,Ct,hCt,hkernel⟩:=full_uniform_canonicalSource_kernel_tail A
  obtain ⟨Cb,hCb,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨s,Cb*128^5*Ct,by positivity,?_⟩
  intro ι _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Γ G₁ G₂ M₁ M₂ Ksrc K ell B F lengthScale
    hΓ hG₁ hG₂ hKsrc hK hell hB hF hL hL₁ hL₂ hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF ha hg₁ hg₂ hM₁ hM₂
  have hB0:0<B:=zero_lt_one.trans_le hB
  have hL0:0<lengthScale:=zero_lt_one.trans_le hL
  let P:=Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let H:ℝ:=(Ksrc/K)/Real.exp (M₁+M₂)
  let Q:ℝ:=(128*lengthScale)^2*(G₁*G₂*Ksrc)*P*(1+lengthScale^3*B^4/Ksrc)^2/(1+H)^A
  have hP:0≤P:=by dsimp [P];positivity
  have hH:0≤H:=by dsimp [H];positivity
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hlabel:(labels.card:ℝ)≤128*F:=DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hbcount:(bs.card:ℝ)≤Cb*B^(1+ε)*B:=by
    apply hcount p hp hinj bs B B hB hB0.le hadm hb₁ hb₂
    intro b hb
    have hn:primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)≤B^2:=
      (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
        (cubeCoordinates_radical_bound p hp b B hB0.le (hb₁ b hb) (hb₂ b hb))
    change ‖eisEmbedding (∏i∈cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖^2≤B^2 at hn
    nlinarith [norm_nonneg (eisEmbedding (∏i∈cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i))]
  let z (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal ActualEisensteinCubic.O):ℂ:=
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I)
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W Ksrc (canonicalSourceCutoff p K ell b C)
  have hblock (b:CubeCoordinates ι) (hb:b∈bs) (C:Finset ι) (hC:C∈boundedPrimeSupports p (pool\b.support) lengthScale) (I:Ideal ActualEisensteinCubic.O):
      ‖z b C I‖≤(128*(lengthScale*B^2))*Q:=by
    have hCb:primeProductNorm p C≤lengthScale:=(Finset.mem_filter.mp hC).2
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hiB=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hiB)
    let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
    let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
    let U₁:=X₁*Real.exp M₁
    let U₂:=X₂*Real.exp M₂
    let E:=primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
    have hU₁:0<U₁:=mul_pos (div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))) (Real.exp_pos _)
    have hU₂:0<U₂:=mul_pos (div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))) (Real.exp_pos _)
    have hE:0<E:=primeProductNorm_pos p hp _
    have hU₁b:U₁≤lengthScale:=(mul_le_mul_of_nonneg_right (div_le_self hell.le
      (one_le_mul_of_one_le_of_one_le (primeProductNorm_ge_one p hp _) (primeProductNorm_ge_one p hp _))) (Real.exp_pos M₁).le).trans hL₁
    have hU₂b:U₂≤lengthScale:=(mul_le_mul_of_nonneg_right (div_le_self hell.le
      (one_le_mul_of_one_le_of_one_le (primeProductNorm_ge_one p hp _) (primeProductNorm_ge_one p hp _))) (Real.exp_pos M₂).le).trans hL₂
    have hEb:E≤B^2:=(primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
      (cubeCoordinates_radical_bound p hp b B hB0.le (hb₁ b hb) (hb₂ b hb))
    have hlocal (D:Finset ι) (hD:D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset):
        ‖∑'h:{h:ActualEisensteinCubic.O // h∉canonicalSourceCutoff p K ell b C D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
          (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
          (canonicalCubeResidual p hg b C true Ψ₁ m₁ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S)))
          (canonicalCubeResidual p hg b C false Ψ₂ m₂ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₂ (columnLog p ell S)))
          W (fun _=>1) (fun _=>1) 1 1 Ksrc (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val‖≤Q:=by
      have hDb:=cubeSourceDivisor_norm_bound p hp b C D B lengthScale hB0.le hL0.le hCB (hb₁ b hb) (hb₂ b hb) hCb (Finset.mem_powerset.mp hD)
      exact (hkernel p hp hinj hcop hg hc pool b (hadm b hb) C D hCB Ψ₁ Ψ₂ hΨ₁ hΨ₂
        m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I) g₁ g₂ W G₁ G₂ M₁ M₂ Ksrc K ell hG₁ hG₂ hKsrc hK hell hg₁ hg₂ hM₁ hM₂).trans
        (firstTail_scalar_bound Ksrc (primeProductNorm p D) E U₁ U₂ lengthScale B G₁ G₂ P H A
          hKsrc (primeProductNorm_pos p hp _) hE hU₁ hU₂ hL0.le hG₁ hG₂ hP hH hDb hEb hU₁b hU₂b)
    dsimp only [z,canonicalCubeDualTail]
    rw [norm_mul]
    calc
      _ ≤ ‖∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
          (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
          ∑'h:{h:ActualEisensteinCubic.O // h∉canonicalSourceCutoff p K ell b C D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
            (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
            (canonicalCubeResidual p hg b C true Ψ₁ m₁ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S)))
            (canonicalCubeResidual p hg b C false Ψ₂ m₂ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₂ (columnLog p ell S)))
            W (fun _=>1) (fun _=>1) 1 1 Ksrc (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val‖:=
        mul_le_of_le_one_left (norm_nonneg _) (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _)
      _ ≤ ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,Q:=by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro D hD
        rw [norm_mul]
        exact (mul_le_mul (sourceMobiusDivisor_norm_le_one p hp D) (hlocal D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul Q)
      _ = ((C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.card:ℝ)*Q:=by simp
      _ ≤ _:=mul_le_mul_of_nonneg_right (cubeSourceDivisors_card p hp hinj b C B lengthScale hB0 hL0 hCB (hb₁ b hb) (hb₂ b hb) hCb) hQ
  have hcommon (b:CubeCoordinates ι) (hb:b∈bs):
      ‖∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤
      (128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q):=by
    have heq:(∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I)=
        ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,a b C I*z b C I:=by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro C hC hnot
      have hn:¬primeProductNorm p C≤ell*Real.exp M₁:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h.trans hL₁⟩)
      apply Finset.sum_eq_zero
      intro I hI
      rw [show z b C I=0 from canonicalCubeDualTail_support p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ _ g₁ g₂ W ell Ksrc M₁ hell hM₁ hn _,mul_zero]
    rw [heq]
    calc
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,‖a b C I*z b C I‖:=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C hC=>norm_sum_le _ _))
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,Γ*((128*(lengthScale*B^2))*Q):=by
        apply Finset.sum_le_sum
        intro C hC
        apply Finset.sum_le_sum
        intro I hI
        rw [norm_mul]
        exact mul_le_mul (ha b hb C (Finset.mem_filter.mp hC).1 I hI) (hblock b hb C hC I) (norm_nonneg _) hΓ
      _ = ((boundedPrimeSupports p (pool\b.support) lengthScale).card:ℝ)*(labels.card:ℝ)*Γ*((128*(lengthScale*B^2))*Q):=by simp;ring
      _ ≤ _:=by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hΓ
        exact mul_le_mul (boundedPrimeSupports_card_positive p hp hinj _ lengthScale hL0) hlabel (Nat.cast_nonneg _) (by positivity)
  change ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤_
  calc
    _ ≤ ∑b∈bs,‖∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖:=norm_sum_le _ _
    _ ≤ ∑b∈bs,(128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q):=Finset.sum_le_sum hcommon
    _ = (bs.card:ℝ)*((128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q)):=by simp
    _ ≤ (Cb*B^(1+ε)*B)*((128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q)):=
      mul_le_mul_of_nonneg_right hbcount (by positivity)
    _ = _:=by
      dsimp [Q,P,H]
      rw [Real.rpow_add hB0,Real.rpow_add hB0]
      norm_num
      ring
end OAI.SecondPassArithmetic
