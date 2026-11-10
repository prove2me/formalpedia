-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_high_radial_negligible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T23:43:19.226367+00:00
-- url     : https://prove2.me/submissions/cd6cf4bf-bbda-43c0-bcd9-1a55f83240f8

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HighRadialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PaddedPassage
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceRemainders
import Theorems.Thm_OAI_InitialMeanSquare_initial_high_radial_sum
import Theorems.Thm_OAI_InitialMeanSquare_initial_log_harmonic_polynomial
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
import Theorems.Thm_OAI_InitialMeanSquare_initialHighRadialConstant_nonneg
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_apply
import Theorems.Thm_OAI_InitialMeanSquare_initialRayMass_nonneg
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
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)
namespace OAI.InitialMeanSquare
theorem _root_.solution (θ τ A Vmax Cs Ccap : ℝ) (N : ℕ)
    (hN : 38+τ ≤ θ*(N : ℝ)) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hCs : 0 ≤ Cs) (hcap : 1 ≤ Ccap) :
    ∃ C : ℝ,0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
      [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
      (K : Finset ι → Finset ι → Finset O) (Z H U Kmax M ε : ℝ),
      1 ≤ Z → 1 ≤ H → 0 < U → 0 < Kmax → ε ≤ 1 →
      U ≤ Ccap*Z^17 → Kmax ≤ Ccap*Z^17 →
      ∀ (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι)),
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,
        s ray R j ⊆ secondLogSector p ∅ F K R Z M j) →
      ∀ (V₁ V₂ : ℝ → ℂ),
      (∀ t,‖V₁ t‖ ≤ Vmax) → (∀ t,‖V₂ t‖ ≤ Vmax) →
      (∀ t,V₁ t ≠ 0 → |t| ≤ A) → (∀ t,V₂ t ≠ 0 → |t| ≤ A) →
      ∀ (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ) (J : ℕ),
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,0 ≤ B ray R j q) →
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B ray R j q ≤
        Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) →
      initialHighRadialCost p hp hcop hg F Ψ m s B Z H U Kmax ε θ V₁ V₂ ≤ C*Z^(-τ) := by
  obtain ⟨Clog,hClog,hlog⟩ := initial_log_harmonic_polynomial
  let Cbase := initialHighRadialConstant A Vmax Cs*initialRayMass*Clog*Ccap^2
  have hfixed := initialHighRadialConstant_nonneg A Vmax Cs hCs
  have hray := initialRayMass_nonneg
  have hbase : 0 ≤ Cbase := by
    dsimp [Cbase]
    exact mul_nonneg (mul_nonneg (mul_nonneg hfixed initialRayMass_nonneg) hClog.le) (sq_nonneg _)
  refine ⟨Cbase+1,by linarith,?_⟩
  intro ι _ p hp _ hcop hg hc hinj F Ψ hΨ m K Z H U Kmax M ε hZ hH hU hK hε hUcap hKcap
    s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J hB hdec
  have hZ0 := zero_lt_one.trans_le hZ
  have hy : 1 ≤ Ccap*Z^17 := one_le_mul_of_one_le_of_one_le hcap (one_le_pow₀ hZ)
  have hlogs := hlog (Ccap*Z^17) U Kmax hy hU hK hUcap hKcap
  have hb := initial_high_radial_sum p hp hcop hg hc hinj F Ψ hΨ m K Z H U Kmax M ε θ
    A Vmax Cs hZ0 hH hε hA hVmax hCs s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J N hB hdec
  have hscalar : Z^(38 : ℕ)/(Z^θ)^N ≤ Z^(-τ) := by
    have he : Z^(38 : ℕ)/(Z^θ)^N=Z^((38 : ℝ)-θ*(N : ℝ)) := by
      rw [Real.rpow_sub hZ0,Real.rpow_mul_natCast hZ0.le]
      norm_cast
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ ≤ (initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass*
        ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) := hb
    _ = ((initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass)*
        (((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ))) := by ring
    _ ≤ ((initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass)*
        (Clog*(Ccap*Z^17)^2) := mul_le_mul_of_nonneg_left hlogs (by positivity)
    _ = Cbase*(Z^(38 : ℕ)/(Z^θ)^N) := by dsimp [Cbase]; ring
    _ ≤ Cbase*Z^(-τ) := mul_le_mul_of_nonneg_left hscalar hbase
    _ ≤ (Cbase+1)*Z^(-τ) := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ0.le _)
end OAI.InitialMeanSquare
