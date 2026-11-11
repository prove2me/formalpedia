-- Prove2me | solution 1 for OAI.SecondPassArithmetic.reopenedCanonicalRow_polynomial_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:19:07.931677+00:00
-- url     : https://prove2.me/submissions/044c5284-18a3-4cd0-adbc-e2f1278a8b12

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopeningBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CutoffOrders
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ClosedRecursion
import Theorems.Thm_OAI_SecondPassArithmetic_reopenedCanonicalRow_state_step
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
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
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstTailFactor_reopening_nat_decay
import Theorems.Thm_OAI_SecondPassArithmetic_reopeningAuxiliaryScale_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_reopeningScaleConstant_one
import Theorems.Thm_OAI_SecondPassArithmetic_reopening_recursive_with_ratio
import Theorems.Thm_OAI_SecondPassArithmetic_reopening_terminal_order
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
    (g V : 𝓢(ℝ,ℂ)) (A M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss η : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (J : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (C : ℝ), 0≤C ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+7) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hpr : ∀i,lambda^2∣p i-1)
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ)
      (Γ t B E : ℝ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 1≤X → X≤Z^3 → F≤Z^3 →
      0≤Γ → 1≤E → 1≤B → B^3≤Real.exp A*X →
      Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B) →
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      B*(∑I∈labels,nonzeroRowMajorantSum
         (reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
           (ConcretePrimeRowBridge.idealGenerator I)
           (fun S=>frequencyTwist g t (columnLog p (X/B^3) S))) Ksrc).re≤
      B*(‖canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (X/B^3)‖+
         ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)+
      C*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε)*E*(1+‖t‖)^(2*J) := by
  obtain ⟨N,hN,hterminal⟩ := reopening_terminal_order η 0 hη
  obtain ⟨w₁,w₂,Cf,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,Clo,Chi,Vmax₁,Vmax₂,
    hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,hClo,hChi,hV₁,hV₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hstep⟩ :=
    reopenedCanonicalRow_state_step g V M Nv hM hNv hgM hV hWin ε deltaLoss hε hδ N J 80
  let Cs:=reopeningScaleConstant A M
  let Tmax:=4096*Cs^20
  have hCs : 1≤Cs:=reopeningScaleConstant_one A M
  have hTmax : 0≤Tmax:=by dsimp [Tmax]; positivity
  let D₁:=canonicalBudgetCoefficient C₁ Cd₁ Ct₁ Tmax Clo Chi (M+7) Vmax₁
  let D₂:=canonicalBudgetCoefficient C₂ Cd₂ Ct₂ Tmax Clo Chi (M+7) Vmax₂
  let Cbase:=Real.exp 5*Cf*Real.sqrt D₁*Real.sqrt D₂
  let Cpow:=((Real.exp 1)^8)^deltaLoss*Cs^(deltaLoss+8*ε)
  have hCbase : 0≤Cbase:=by dsimp [Cbase]; positivity
  have hCpow : 0≤Cpow:=by dsimp [Cpow]; positivity
  refine ⟨w₁,w₂,Cbase*Cpow,mul_nonneg hCbase hCpow,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hcop hg hc hinj hpr base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B E hbase hpbad hZ hZbig hX hXZ hFZ hΓ hE hB hactive hprogress hβ hQ hQB ih
  have hs:=reopeningAuxiliaryScale_bounds A M 1 Z η X F Ksrc B (by norm_num) hZ.le hη.le
    hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hstate.row_le_global hB hactive
  norm_num [reopeningAuxiliaryScale,Real.rpow_natCast] at hs
  obtain ⟨hU,hKU,hellU,hBU,hFU,hHU,heU,hMU,hiU⟩:=hs
  have htail : globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
      (Cs*Z^4) Z 80≤Tmax := by
    have hh:=globalFirstTailFactor_reopening_nat_decay A M Z η X F Ksrc B 0
      hZ.le hη.le hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hstate.row_le_global hB hactive
    simpa only [Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one,zero_add] using hh
  have ht : (Ksrc/Z^η)/Z^(η*(N:ℝ))≤1 := by
    simpa only [neg_zero,Real.rpow_zero] using hterminal Z Ksrc hZ.le
      (zero_le_one.trans hstate.row_ge_one) hstate.row_le_global
  have hb:=hstep p hp hcop hg hc hinj hpr base bad Z η Ψ m labels X F Ksrc hstate pool Q β
    Γ t B Z (Cs*Z^(4:ℕ)) Tmax E hbase hpbad hZ hZbig hη.le hηsmall hΓ hE hU hB
    (zero_le_one.trans hZ.le) hTmax hKU hellU hBU hHU heU hMU hprogress hβ hQ hQB htail ht ih
  dsimp only at hb ⊢
  have hm:=reopening_recursive_with_ratio A M Z η X F Ksrc B deltaLoss ε hZ.le hη.le
    (by linarith) hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hB hδ.le hε.le
  have hx := mul_le_mul_of_nonneg_left hm
    (show 0≤Cbase*Γ^2*(X*F)^2*E*(1+‖t‖)^(2*J) by positivity)
  apply hb.trans
  apply add_le_add le_rfl
  convert hx using 1 <;> dsimp [Cbase,Cpow,D₁,D₂,Cs] <;> ring
end OAI.SecondPassArithmetic
