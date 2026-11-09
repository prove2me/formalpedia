-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.poissonComparisonMajorant_unit_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:24:45.40223+00:00
-- url     : https://prove2.me/submissions/f41b4c8e-75dd-44c2-8fab-dd3262857c96

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_HyperbolicVolume
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_UniformTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GlobalBinLoss
import Theorems.Thm_OAI_QRH_b83dbbd_CanonicalQuadraticSieve_poisson_nine_terms_box
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisorEnergyFactor_diagonal
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
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
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
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T U S : ℝ) (W : 𝓢(ℝ,ℂ))
    (hK : 0≤K) (hN : 0<N) (hM : 0≤M) (hT : 1≤T) (hU : 1≤U) (hS : 0≤S)
    (hbudget : ∀x∈poissonUnitBudget sD sS sT CD CS CT CP hexp deltaLoss hδ ε hε G K N W, 0≤x ∧ x≤U)
    (hMS : M≤S) (hNS : N≤S) (hmid : T*Real.sqrt M*(2*K)^(α-1/2)≤S)
    (hpr : Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2)≤S)
    (hED : K*M/T^l≤S) (hES : K*N/T^l≤S)
    (htail : M/((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
      (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)≤S) :
    poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T
      (fun _ : Unit => (1:ℂ)) W ≤ 262144*U^8*S := by
  have hh := poisson_nine_terms_box
    ((IdealMobiusDivisorSum.idealDivisors G).card:ℝ)
    (columnDyadicLength K+1:ℕ) (columnDyadicLength N+1:ℕ)
    (256*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)
    (divisorExponentConstant hexp deltaLoss hδ*((2*K)*N)^deltaLoss)
    ‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖
    ‖quadraticTransformedSquareProfile W 0‖
    (dualMiddleDecayConstant (quadraticTransformedSquareProfile W))
    ‖paperRadialFourier (quadraticSquareProfile W) 0‖
    (originalMiddleDecayConstant (quadraticSquareProfile W)) nonzeroLatticeEnvelopeConstant
    (supportConstant ε hε*(N*N)^ε*(CD*sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)))
    (supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε*(CS*sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)))
    (CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    (supportConstant ε hε*N^ε*CP*(K*N)^deltaLoss)
    M N T (Real.sqrt M*(2*K)^(α-1/2))
    (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))
    (K*M/T^l) (K*N/T^l)
    (M/((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*(1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A))
    U S hU hS hbudget hM hN.le hT (by positivity) hMS hNS
    (by simpa only [mul_assoc] using hmid) ⟨by positivity,hpr⟩
    ⟨by positivity,hED⟩ ⟨by positivity,hES⟩ ⟨by positivity,htail⟩
  convert hh using 1
  unfold poissonComparisonMajorant retainedDualMajorant sourcePrincipalMajorant
    smallPrincipalMajorant dualMiddleMajorant
  simp only [divisorEnergyFactor_diagonal,Fintype.sum_unique,norm_one,one_pow,
    mul_one,one_mul,div_one]
  field_simp
  ; ring
end OAI.CanonicalQuadraticSieve
