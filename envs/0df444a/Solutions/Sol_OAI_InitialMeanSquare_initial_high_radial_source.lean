-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_high_radial_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T23:51:05.040818+00:00
-- url     : https://prove2.me/submissions/e0dc8358-c1cc-4ac6-8e44-cbab0d570ac7

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HighRadialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PaddedPassage
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceRemainders
import Theorems.Thm_OAI_InitialMeanSquare_initial_high_radial_order
import Theorems.Thm_OAI_InitialMeanSquare_initial_high_radial_negligible
import Theorems.Thm_OAI_InitialMeanSquare_initialErrorRowBound_pos
import Theorems.Thm_OAI_InitialMeanSquare_initialPolynomialCap_ge_one
import Theorems.Thm_OAI_InitialMeanSquare_initial_actual_bin_polynomial_caps
import Theorems.Thm_OAI_InitialMeanSquare_initial_two_windows_bounded
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
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_apply
import Theorems.Thm_OAI_InitialMeanSquare_initial_subbin_transfer
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
open OAI.InitialMeanSquare
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity normalizedColumn columnLog)
namespace OAI.InitialMeanSquare
theorem _root_.solution
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b θ τ ε : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hθ : 0 < θ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ,0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (Z H : ℝ),
      1 ≤ Z → 1 ≤ H → (∀ x,‖Ψ x‖ ≤ 1) →
      ∀ (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι)),
      (∀ ray R j,s ray R j ⊆ secondLogSector p ∅ F
        (fun _ _ => initialErrorCutoff a b Z H) R Z (initialErrorWindow a b) j) →
      let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if Z^θ < initialRadial Z H (primeProductNorm p R) j then
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray (s ray R j) G G W H‖ else 0) ≤
      C*Z^(-τ) := by
  obtain ⟨N,hN⟩ := initial_high_radial_order θ τ hθ
  have hM : 0 ≤ initialErrorWindow a b := by unfold initialErrorWindow; positivity
  obtain ⟨windows,Ct,Cs,hCt,hCs,hwc,hws,ht⟩ :=
    initial_subbin_transfer U hUc hUs g W (initialErrorWindow a b) hM hU hgs ε hε (N+2) 0
  obtain ⟨A,Vmax,hA,hVmax,hV₁,hV₂,hs₁,hs₂⟩ :=
    initial_two_windows_bounded (windows 5) (windows 6) (hwc 5) (hwc 6)
      (hws 5).continuous (hws 6).continuous
  obtain ⟨Ch,hCh,hh⟩ := initial_high_radial_negligible θ τ A Vmax Cs (initialPolynomialCap a b)
    N hN hA hVmax hCs (initialPolynomialCap_ge_one a b)
  refine ⟨Ct*Ch+1,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m Z H hZ hH hΨ s hs
  dsimp only
  have hZ0 := zero_lt_one.trans_le hZ
  have hH0 := zero_lt_one.trans_le hH
  let K := fun (_ _ : Finset ι) => initialErrorCutoff a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H (initialErrorWindow a b) j
        (s ray R j) hZ0 hH0 hΨ (hs ray R j))
  have hB (ray : SecondRayIndex) (R : Finset ι) (j : SecondLogIndex) :=
    Classical.choose_spec
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H (initialErrorWindow a b) j
        (s ray R j) hZ0 hH0 hΨ (hs ray R j))
  have hcost := hh p hp hcop hg hc hinj F Ψ hΨ m K Z H
    (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H)
    (initialErrorWindow a b) ε hZ hH (by positivity) (initialErrorRowBound_pos a b Z H hZ0 hH0)
    hε1 (initial_actual_bin_polynomial_caps a b Z H hZ hH).1
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).2
    s (fun ray R _ j _ => hs ray R j) (windows 5) (windows 6) hV₁ hV₂ hs₁ hs₂ B 0
    (fun ray R _ j _ => (hB ray R j).1) (fun ray R _ j _ => (hB ray R j).2.1)
  have hsum :
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if Z^θ < initialRadial Z H (primeProductNorm p R) j then
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray (s ray R j) G G W H‖ else 0) ≤
      Ct*initialHighRadialCost p hp hcop hg F Ψ m s B Z H
        (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H) ε θ (windows 5) (windows 6) := by
    unfold initialHighRadialCost
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ray hray
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with hjrad
    · convert (hB ray R j).2.2 using 1 <;> first | rfl | (dsimp only [initialRestrictedBinCost,G,B]; ring)
    · simp
  calc
    _ ≤ Ct*initialHighRadialCost p hp hcop hg F Ψ m s B Z H
        (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H) ε θ (windows 5) (windows 6) := hsum
    _ ≤ Ct*(Ch*Z^(-τ)) := mul_le_mul_of_nonneg_left hcost hCt
    _ ≤ (Ct*Ch+1)*Z^(-τ) := by
      have hz := Real.rpow_nonneg hZ0.le (-τ)
      nlinarith
end OAI.InitialMeanSquare
