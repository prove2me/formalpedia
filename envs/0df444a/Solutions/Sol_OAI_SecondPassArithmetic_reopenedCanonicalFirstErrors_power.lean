-- Prove2me | solution 1 for OAI.SecondPassArithmetic.reopenedCanonicalFirstErrors_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:48:38.727928+00:00
-- url     : https://prove2.me/submissions/e7864080-da1a-4f2a-bc11-0718ffac6689

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
import Theorems.Thm_OAI_SecondPassArithmetic_CanonicalStateCondition_row_bound
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalFirstTail_reopening_order
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalFirstZero_normalization
import Theorems.Thm_OAI_SecondPassArithmetic_reopenedCanonicalFirstErrors
import Theorems.Thm_OAI_SecondPassArithmetic_reopeningAuxiliaryScale_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_reopeningScaleConstant_one
import Theorems.Thm_OAI_SecondPassArithmetic_reopening_cube_bound
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
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (g : 𝓢(ℝ,ℂ)) (A M : ℝ) (hgM : ∀t,g t≠0→|t|≤M)
    (ε η : ℝ) (hε : 0<ε) (hη : 0<η) (hbudget : 3000*η≤(1:ℝ)/40) :
    ∃C : ℝ,0≤C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ)
      (Γ t B : ℝ),
      (∀u,‖base u‖≤1) → 1≤Z → 1≤X → X≤Z^3 → F≤Z^3 →
      0≤Γ → 1≤B → B^3≤Real.exp A*X →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      B*(‖canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (X/B^3)‖+
         ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)≤
      C*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40) := by
  obtain ⟨N,hN,horder⟩:=canonicalFirstTail_reopening_order η ε ((1:ℝ)/40) hη hε.le
  obtain ⟨Cz,Ct,hCz,hCt,herrors⟩:=reopenedCanonicalFirstErrors g M hgM ε hε N
  let Cs:=reopeningScaleConstant A M
  have hCs : 1≤Cs:=reopeningScaleConstant_one A M
  let Cz':=Cz*(Real.exp 1)^(1+ε)*Cs^ε
  let Ct':=4*Ct*(Real.exp (2*M))^N*Cs^(25+ε)
  have hCz' : 0≤Cz':=by dsimp [Cz']; positivity
  have hCt' : 0≤Ct':=by dsimp [Ct']; positivity
  refine ⟨Cz'+Ct',add_nonneg hCz' hCt',?_⟩
  intro ι _ p hp _ hcop hg hinj hc base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B hbase hZ hX hXZ hFZ hΓ hB hactive hβ hQB
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hX0 : 0<X:=zero_lt_one.trans_le hX
  have hB0 : 0<B:=zero_lt_one.trans_le hB
  have hK0 : 0<Ksrc:=zero_lt_one.trans_le hstate.row_ge_one
  have hF0 : 0<F:=zero_lt_one.trans_le hstate.label_ge_one
  have hs:=reopeningAuxiliaryScale_bounds A M 1 Z η X F Ksrc B (by norm_num) hZ hη.le
    hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hstate.row_le_global hB hactive
  norm_num [reopeningAuxiliaryScale,Real.rpow_natCast] at hs
  obtain ⟨hU,hKU,hellU,hBU,hFU,hHU,heU,hMU,hiU⟩:=hs
  let U:=Cs*Z^(4:ℕ)
  have hBsup : 1≤Real.exp 1*B:=one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  have hB0U : B≤U := (le_mul_of_one_le_left hB0.le (Real.one_le_exp (by norm_num))).trans hBU
  have hKsrcU : Ksrc≤U := by
    calc
      _ ≤ Z^3:=hstate.row_le_global
      _ ≤ Z^4:=by nlinarith [sq_nonneg Z,show 0≤Z^2*(Z-1)^2 by positivity]
      _ ≤ U:=le_mul_of_one_le_left (by positivity) hCs
  have herr:=herrors p hp hcop hg hinj hc pool Q labels β Ψ m Γ t Ksrc (Ksrc/Z^η)
    (X/B^3) (Real.exp 1*B) F U hΓ hK0 (by positivity) (by positivity) hBsup
    hstate.label_ge_one hU hMU (fun u=>hstate.coefficient.norm_le hbase u) hβ hQB
    (fun I hI=>(hstate.label_bounds I hI).1) (fun I hI=>(hstate.label_bounds I hI).2.2.2)
  dsimp only at herr ⊢
  have hzero:=canonicalFirstZero_normalization Cz Γ X F Ksrc B Z ε hCz hX0 hF0.le hK0.le hB
    (hstate.row_bound hZ hη.le hbudget)
  have hBpow : B^ε≤Cs^ε*Z^(3*ε) := by
    have hh : B≤Cs*Z^3 := (le_mul_of_one_le_left hB0.le (Real.one_le_exp (by norm_num))).trans
      (reopening_cube_bound A M Z X B hZ hX hXZ hB hactive)
    apply (Real.rpow_le_rpow hB0.le hh hε.le).trans_eq
    rw [Real.mul_rpow (by linarith) (by positivity),←Real.rpow_natCast_mul hZ0.le]
    norm_num
  have hz : B*‖canonicalSourceZero p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (X/B^3)‖≤
      Cz'*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40) := by
    apply ((mul_le_mul_of_nonneg_left herr.1 hB0.le).trans hzero).trans
    calc
      _ ≤ (Cz*(Real.exp 1)^(1+ε))*(Cs^ε*Z^(3*ε))*Γ^2*(X*F)^2*Z^(-((1:ℝ)/40)) := by gcongr
      _ = _ := by rw [show 3*ε-(1:ℝ)/40=3*ε+(-((1:ℝ)/40)) by ring,Real.rpow_add hZ0]; dsimp [Cz']; ring
  have ht0:=horder Cs Ct Γ B (Real.exp 1*B) U F Ksrc Z M hCs hCt hB0.le
    (by positivity) (by positivity) hF0.le hstate.row_ge_one hZ hB0U hBU le_rfl hFU hKsrcU
  have ht : B*‖canonicalSourceTail p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖≤
      Ct'*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40) := by
    have hpow : Z^(-((1:ℝ)/40))≤Z^(3*ε-(1:ℝ)/40):=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    have hXF : 1≤(X*F)^2:=one_le_pow₀ (one_le_mul_of_one_le_of_one_le hX hstate.label_ge_one)
    apply ((mul_le_mul_of_nonneg_left herr.2 hB0.le).trans ht0).trans
    calc
      _ = Ct'*Γ^2*Z^(-((1:ℝ)/40)):=by dsimp [Ct']; ring
      _ ≤ Ct'*Γ^2*((X*F)^2*Z^(3*ε-(1:ℝ)/40)):=by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCt' (sq_nonneg Γ))
        exact hpow.trans (le_mul_of_one_le_left (by positivity) hXF)
      _ = _:=by ring
  rw [mul_add]
  exact (add_le_add hz ht).trans_eq (by ring)
end OAI.SecondPassArithmetic
