-- Prove2me | solution 1 for OAI.SecondPassArithmetic.reopenedCanonicalRow_state_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:05:10.721747+00:00
-- url     : https://prove2.me/submissions/2a38e4f0-2428-46d9-88fc-a24649988cff

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopeningBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CutoffOrders
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ClosedRecursion
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCoefficientClass_IsBaseRayTwist_norm_le
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedWeight_apply
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
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalBudgetCoefficient_nonneg
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalPairBudget_normalized
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalSourceBlocks_cube_norms
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstQuantitativeBudget_bounded
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstRowCap_pos
import Theorems.Thm_OAI_SecondPassArithmetic_reopenedCanonicalRow_nonzero_twoPassage
import Theorems.Thm_OAI_SecondPassArithmetic_reopenedCubeFamily_cube_norms
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CanonicalCubeSeparation.cubeFrequencyFactor_norm
attribute [local simp] OAI.CanonicalCubeSeparation.sourceLogProfile_apply
attribute [local simp] OAI.CanonicalRowCompletion.cubeIndex_apply
attribute [local simp] OAI.CompletedHeight.completedT_normHeight_norm
attribute [local simp] OAI.CompletedHeight.shortCompletedSum_normHeight_norm
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_apply
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_source
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.kernelLocalLift_symm
attribute [local simp] OAI.CubicEisenstein.kernelQuotientChart_symm
attribute [local simp] OAI.CubicEisenstein.kernelTruncatedWeight_apply
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


section
namespace OAI
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
namespace SecondPassArithmetic
section
open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)
private theorem two_windows_bound (windows : Fin 7→ℝ→ℂ)
    (hc : ∀i,HasCompactSupport (windows i)) (hs : ∀i,Continuous (windows i)) :
    ∃Vmax : ℝ,0≤Vmax ∧ (∀t,‖windows 5 t‖≤Vmax) ∧ (∀t,‖windows 6 t‖≤Vmax) := by
  have hb (i : Fin 7) : ∃B : ℝ,0≤B ∧ ∀t,‖windows i t‖≤B := by
    obtain ⟨B,hB⟩ := ((hc i).isCompact_range (hs i)).bddAbove_image continuous_norm.continuousOn
    have he (t : ℝ) : ‖windows i t‖≤B := hB ⟨windows i t,⟨t,rfl⟩,rfl⟩
    exact ⟨B,(norm_nonneg _).trans (he 0),he⟩
  obtain ⟨B₅,h₅,hb₅⟩ := hb 5
  obtain ⟨B₆,h₆,hb₆⟩ := hb 6
  exact ⟨B₅+B₆,by linarith,fun t=>(hb₅ t).trans (by linarith),fun t=>(hb₆ t).trans (by linarith)⟩
end
open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)
end SecondPassArithmetic
open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic UniqueFactorizationMonoid
end CompletedGauss
open Filter MeasureTheory
open scoped BigOperators Classical Topology
namespace CubicEisenstein
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
end CubicEisenstein
end
end OAI
end

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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (g V : 𝓢(ℝ,ℂ)) (M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (N J Ntail : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ)
      (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ Clo Chi Vmax₁ Vmax₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧ 0<Clo ∧ 0<Chi ∧
      0≤Vmax₁ ∧ 0≤Vmax₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+7) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hpr : ∀i,lambda^2∣p i-1)
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ)
      (Γ t B H U Tmax E : ℝ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 0≤η → η≤(1:ℝ)/1000 →
      0≤Γ → 1≤E → 1≤U → 1≤B → 0≤H → 0≤Tmax →
      Ksrc/Z^η≤U → X/B^3≤U → Real.exp 1*B≤U → H≤U → Real.exp M≤U →
      (X/B^3)*Real.exp M≤U → Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B) →
      globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail≤Tmax →
      (Ksrc/Z^η)/Z^(η*(N:ℝ))≤1 →
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      let D₁:=canonicalBudgetCoefficient C₁ Cd₁ Ct₁ Tmax Clo Chi (M+7) Vmax₁
      let D₂:=canonicalBudgetCoefficient C₂ Cd₂ Ct₂ Tmax Clo Chi (M+7) Vmax₂
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      B*(∑I∈labels,nonzeroRowMajorantSum
         (reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
           (ConcretePrimeRowBridge.idealGenerator I)
           (fun S=>frequencyTwist g t (columnLog p (X/B^3) S))) Ksrc).re≤
      B*(‖canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (X/B^3)‖+
         ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)+
      (Real.exp 5*Cfirst*Real.sqrt D₁*Real.sqrt D₂)*Γ^2*(X*F)^2*
        (Ksrc/(Ksrc/Z^η))*(globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss*
        U^(deltaLoss+8*ε)*E*(1+‖t‖)^(2*J) := by
  obtain ⟨w₁,w₂,Cf,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,htransfer⟩ :=
    reopenedCanonicalRow_nonzero_twoPassage g V M Nv hM hNv hgM hV hWin ε deltaLoss hε hδ (N+1) (2*J) Ntail
  obtain ⟨Clo,Chi,hClo,hChi,hbudget⟩ := globalFirstQuantitativeBudget_bounded deltaLoss hδ ε hε
  obtain ⟨Vmax₁,hVmax₁,hw₁₅,hw₁₆⟩ := two_windows_bound w₁ hwc₁ (fun i=>(hws₁ i).continuous)
  obtain ⟨Vmax₂,hVmax₂,hw₂₅,hw₂₆⟩ := two_windows_bound w₂ hwc₂ (fun i=>(hws₂ i).continuous)
  have hwb₁' : ∀i t,w₁ i t≠0→|t|≤M+7 := by convert hwb₁ using 1 ; ring_nf
  have hwb₂' : ∀i t,w₂ i t≠0→|t|≤M+7 := by convert hwb₂ using 1 ; ring_nf
  refine ⟨w₁,w₂,Cf,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,Clo,Chi,Vmax₁,Vmax₂,
    hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,hClo,hChi,hVmax₁,hVmax₂,
    hwc₁,hws₁,hwb₁',hwc₂,hws₂,hwb₂',?_⟩
  intro ι _ p hp _ hcop hg hc hinj hpr base bad Z η Ψ m labels X F Ksrc hstate pool Q β
    Γ t B H U Tmax E hbase hpbad hZ hZbig hη hηsmall hΓ hE hU hB hH hTmax hKU hellU hBU hHU heU
    hMU hprogress hβ hQ hQB htail hterminal ih
  dsimp only
  have hX:=hstate.column_pos
  have hF0 : 0<F:=zero_lt_one.trans_le hstate.label_ge_one
  have hK0 : 0<Ksrc:=zero_lt_one.trans_le hstate.row_ge_one
  have hB0 : 0<B:=zero_lt_one.trans_le hB
  have hell : 0<X/B^3:=div_pos hX (pow_pos hB0 _)
  have hKcut : 0<Ksrc/Z^η:=div_pos hK0 (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  have hBsup : 1≤Real.exp 1*B:=one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  have hΨ : ∀u,‖Ψ u‖≤1:=fun u=>hstate.coefficient.norm_le hbase u
  have he := htransfer p hp hinj hcop hg hc hpr pool Q labels β Ψ m Γ t Ksrc (Ksrc/Z^η)
    (X/B^3) (Real.exp 1*B) F H U hΓ hK0 hKcut hell hBsup hF0 hH hU hMU hΨ hβ hQ hQB
    (fun I hI=>(hstate.label_bounds I hI).2.1) (fun I hI=>(hstate.label_bounds I hI).2.2.2)
  let blocks:=canonicalSourceBlocks pool (reopenedCubeFamily Q)
  have hb₁ : ∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤Real.exp 1*B:=
    fun b hb=>(canonicalSourceBlocks_cube_norms p pool (reopenedCubeFamily Q) (Real.exp 1*B)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).1)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).2) b hb).1
  have hb₂ : ∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤Real.exp 1*B:=
    fun b hb=>(canonicalSourceBlocks_cube_norms p pool (reopenedCubeFamily Q) (Real.exp 1*B)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).1)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).2) b hb).2
  have hbL:=hbudget p hp hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate pool blocks true w₁
    C₁ Cd₁ Ct₁ Tmax (Γ^2) E t B M H U (M+7) Vmax₁ N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC₁ hCd₁.le hCt₁.le hTmax (sq_nonneg Γ) hE hU hB hH
    hKU hellU hBU hHU heU hprogress (by linarith) hVmax₁ hw₁₅ hw₁₆ (hwb₁' 5) (hwb₁' 6)
    hb₁ hb₂ htail hterminal (ih true)
  have hbR:=hbudget p hp hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate pool blocks false w₂
    C₂ Cd₂ Ct₂ Tmax (Γ^2) E t B M H U (M+7) Vmax₂ N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC₂ hCd₂.le hCt₂.le hTmax (sq_nonneg Γ) hE hU hB hH
    hKU hellU hBU hHU heU hprogress (by linarith) hVmax₂ hw₂₅ hw₂₆ (hwb₂' 5) (hwb₂' 6)
    hb₁ hb₂ htail hterminal (ih false)
  let D₁:=canonicalBudgetCoefficient C₁ Cd₁ Ct₁ Tmax Clo Chi (M+7) Vmax₁
  let D₂:=canonicalBudgetCoefficient C₂ Cd₂ Ct₂ Tmax Clo Chi (M+7) Vmax₂
  have hD₁ : 0≤D₁:=canonicalBudgetCoefficient_nonneg _ _ _ _ _ _ _ _ hC₁ hCd₁.le hCt₁.le hTmax hClo.le hChi.le
  have hD₂ : 0≤D₂:=canonicalBudgetCoefficient_nonneg _ _ _ _ _ _ _ _ hC₂ hCd₂.le hCt₂.le hTmax hClo.le hChi.le
  have hpairs:=canonicalPairBudget_normalized X F B Ksrc (Ksrc/Z^η) Cf
    ((globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss) U (deltaLoss+8*ε) E t
    (D₁*Γ^2) (D₂*Γ^2) _ _ J hX hF0.le hB0 hK0.le hKcut hCf
    (Real.rpow_nonneg (globalFirstRowCap_pos _ _ _ _ hKcut hell (zero_lt_one.trans_le hBsup) hF0).le _)
    (zero_le_one.trans hU) (zero_le_one.trans hE) (mul_nonneg hD₁ (sq_nonneg Γ)) (mul_nonneg hD₂ (sq_nonneg Γ))
    (by simpa only [mul_assoc] using hbL) (by simpa only [mul_assoc] using hbR)
  have hsqrt : Real.sqrt (D₁*Γ^2)*Real.sqrt (D₂*Γ^2)=Real.sqrt D₁*Real.sqrt D₂*Γ^2 := by
    rw [Real.sqrt_mul hD₁,Real.sqrt_mul hD₂,Real.sqrt_sq_eq_abs]
    calc
      _ = Real.sqrt D₁*Real.sqrt D₂*(|Γ|^2) := by ring
      _ = _ := by rw [sq_abs]
  have hscaled:=mul_le_mul_of_nonneg_left he hB0.le
  calc
    _ ≤ B*(‖canonicalSourceZero p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
        (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (X/B^3)‖+
       ‖canonicalSourceTail p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
        (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)+
       B*((X/B^3)*(Real.exp 1*B)^2*F*(Ksrc/(Ksrc/Z^η))*Cf*
         (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss*
         Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ t) m w₁
           C₁ Cd₁ Ct₁ (Γ^2) ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail true)*
         Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ t) m w₂
           C₂ Cd₂ Ct₂ (Γ^2) ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail false)) :=
      hscaled.trans_eq (by ring)
    _ ≤ _ := by
      apply (add_le_add le_rfl hpairs).trans_eq
      calc
        _ = _ := by rw [show Real.exp 5*Cf*Real.sqrt (D₁*Γ^2)*Real.sqrt (D₂*Γ^2)=
            Real.exp 5*Cf*(Real.sqrt (D₁*Γ^2)*Real.sqrt (D₂*Γ^2)) by ring,hsqrt];ring
end OAI.SecondPassArithmetic
