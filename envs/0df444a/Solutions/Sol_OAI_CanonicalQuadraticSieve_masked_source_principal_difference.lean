-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.masked_source_principal_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T00:56:13.605603+00:00
-- url     : https://prove2.me/submissions/eacdadbc-7e9d-4ba0-b964-4f1fdb04f037

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_RetainedDualBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
import Theorems.Thm_OAI_CanonicalQuadraticSieve_maskedPrincipalSourceSum_eq
import Theorems.Thm_OAI_CanonicalQuadraticSieve_maskedSource_error_uniform
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_masked_source_large_principal_sum
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_original_masked_truncated_middle
import Theorems.Thm_OAI_CanonicalQuadraticSieve_norm_four_correction_terms
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
open scoped BigOperators Classical SchwartzMap
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator IdealMobiusDivisorSum
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
        (G : Ideal O), Squarefree G →
      ∀ (B N M T : ℝ), 1≤B → 1≤N → 0<M → 4≤T →
      ∀ (rows : m → Ideal O) (cols : n → Ideal O),
        Function.Injective rows → Function.Injective cols →
        (∀ i, Admissible (rows i) ∧ B/2≤(Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ)≤B) →
        (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀ j, IsCoprime G (cols j)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖maskedPrincipalSourceSum G W rows cols a M -
          paperRadialFourier W 0*maskedSourceDensity G rows cols a M‖ ≤
        sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G B N M T a W := by
  obtain ⟨s,C,hC,herr⟩ := maskedSource_error_uniform l
  refine ⟨s,C,hC,?_⟩
  intro m n _ _ _ _ α hexp deltaLoss hδ ε hε G hG B N M T hB hN hM hT rows cols hr hc hrows hcols hGc a W hW
  let Z := fun i => T*sourcePrincipalScale M (rows i)
  let Y := fun i => sourcePrincipalScale M (rows i)/T
  have hT0 : 0≤T := by linarith
  have hsplit := maskedPrincipalSourceSum_eq G hG W hW rows cols a M T (fun j => (hcols j).1) hGc
  change maskedPrincipalSourceSum G W rows cols a M =
    paperRadialFourier W 0*maskedSourceDensity G rows cols a M -
    paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z +
    originalMaskedTruncatedMiddle G W rows cols cols a a M Y Z (T^4) +
    maskedSourceErrorSum G W rows cols a M T at hsplit
  have heq : maskedPrincipalSourceSum G W rows cols a M -
      paperRadialFourier W 0*maskedSourceDensity G rows cols a M =
      -(paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z) +
      originalMaskedTruncatedMiddle G W rows cols cols a a M Y Z (T^4) +
      maskedSourceErrorSum G W rows cols a M T := by rw [hsplit]; ring
  have hl := hexp.masked_source_large_principal_sum deltaLoss hδ ε hε G hG.ne_zero B N M T hB hN hM (by linarith)
    rows cols cols hr hc hc hrows hcols hcols hGc hGc a a Z (fun _ => le_rfl)
  have hm := hexp.original_masked_truncated_middle deltaLoss hδ ε hε G hG B N M T hB hN hM hT0
    rows cols cols hr hc hc hrows a a W Y Z (T^4) hcols hcols hGc hGc (fun _ => le_rfl)
  have he := herr ε hε G hG.ne_zero B N M T hB hN hM hT rows cols hr hc
    (fun i => ⟨(hrows i).1.1,(hrows i).2.2⟩) (fun j => ⟨(hcols j).1.1,(hcols j).2⟩) a W
  have hn := norm_four_correction_terms
    (paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z) 0
    (originalMaskedTruncatedMiddle G W rows cols cols a a M Y Z (T^4))
    (maskedSourceErrorSum G W rows cols a M T)
  simp only [sub_zero,norm_zero,add_zero] at hn
  rw [heq]
  apply hn.trans
  rw [norm_mul]
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hl (norm_nonneg _)) hm) he
end OAI.CanonicalQuadraticSieve
