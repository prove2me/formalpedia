-- Prove2me | solution 1 for OAI.QRH_b83dbbd.CanonicalQuadraticSieve.HasSieveExponent.masked_poisson_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:21:05.861619+00:00
-- url     : https://prove2.me/submissions/36b6afcd-af76-4237-bd6f-9d0c15de4a74

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonComparison
import Theorems.Thm_OAI_CanonicalQuadraticSieve_maskedPoissonDifference_norm_le
import Theorems.Thm_OAI_QRH_b83dbbd_CanonicalQuadraticSieve_centeredRetainedDual_sum_bound
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_actual_principal_difference
import Theorems.Thm_OAI_CanonicalQuadraticSieve_coprimeSquarefreeRange_subset_idealRange
import Theorems.Thm_OAI_CanonicalQuadraticSieve_densityColumn_energy_le
import Theorems.Thm_OAI_CanonicalQuadraticSieve_maskedDualTailFamily_bound
import Theorems.Thm_OAI_CanonicalQuadraticSieve_masked_source_principal_global
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
import Theorems.Thm_OAI_IdealCoprimeSieveOperator_supportConstant_pos
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
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator
namespace OAI.CanonicalQuadraticSieve
namespace HasSieveExponent
theorem _root_.solution {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (ε : ℝ) (hε : 0<ε)
        (G : Ideal OAI.CanonicalQuadraticSieve.O), Squarefree G → (∀P∈fixedBadPrimes,P∣G) →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 1≤M → 4≤T →
      ∀ (cols : n → Ideal OAI.CanonicalQuadraticSieve.O), Function.Injective cols →
        (∀j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀j k, columnRay (cols j)=columnRay (cols k)) → (∀j, IsCoprime G (cols j)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖(6:ℂ)*maskedPoissonDifference G W cols a M K‖ ≤
          poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T a W := by
  obtain ⟨sD,CD,hCD,hdual⟩ := centeredRetainedDual_sum_bound l
  obtain ⟨sS,CS,hCS,hsource⟩ := masked_source_principal_global l
  obtain ⟨sT,CT,hCT,htail⟩ := maskedDualTailFamily_bound A
  obtain ⟨CP,hCP,hprincipal⟩ := hexp.actual_principal_difference deltaLoss hδ
  refine ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,?_⟩
  intro n _ _ ε hε G hG hbad K N M T hK hN hM hT cols hc hcols hray hGc a W hW
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hcols0 : ∀j, Admissible (cols j) := fun j => (hcols j).1
  have hcolsu : ∀j, Admissible (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤N :=
    fun j => ⟨(hcols j).1,(hcols j).2.2⟩
  have hd := hdual hexp hα deltaLoss hδ ε hε G hG.ne_zero K N M T hK hN hM0 hT cols hc hcols hray a W
  have hs := hsource hexp hα deltaLoss hδ ε hε G hG K N M T hK hN hM0 hT
    (coprimeSquarefreeRange G K)
    (fun I hI => mem_idealRange.mp (coprimeSquarefreeRange_subset_idealRange G hbad K hI))
    cols hc hcolsu hGc a (quadraticSquareProfile W)
    (by simpa only [quadraticSquareProfile_apply,zero_pow (by decide : 2≠0)] using hW)
  have ht := htail G cols a W M N K hG.ne_zero hc hM0 hN (by linarith)
    (fun j => ⟨(hcols j).1.1,(hcols j).2⟩)
  have hp := hprincipal cols hc M N K hM hN hK hcolsu hray
    (densityColumn cols a) G hG hbad ε hε
  have he := densityColumn_energy_le cols a (fun j => (hcols j).1.1)
  have hsupp := (supportConstant_pos ε hε).le
  have hp' : ‖(Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K‖ ≤
      ((idealDivisors G).card:ℝ)^2*(supportConstant ε hε*N^ε)*CP*(K*N)^deltaLoss*
        (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))*∑j, ‖a j‖^2 := by
    apply hp.trans
    gcongr
  have hmain := maskedPoissonDifference_norm_le G hG.ne_zero W cols a M K hM0 hcols0 hray hGc hbad
  apply hmain.trans
  change _ ≤ _+_+_+_
  have hs' : ‖centeredMaskedSource G W cols a M K‖ ≤
      (columnDyadicLength K+1:ℕ)*sourcePrincipalMajorant sS CS l hexp deltaLoss hδ ε hε G (2*K) N M T a
        (quadraticSquareProfile W) := hs
  exact add_le_add (add_le_add (add_le_add hd (mul_le_mul_of_nonneg_left ht (by norm_num))) hs')
    (mul_le_mul_of_nonneg_left hp' (norm_nonneg _))
end HasSieveExponent
end OAI.CanonicalQuadraticSieve
