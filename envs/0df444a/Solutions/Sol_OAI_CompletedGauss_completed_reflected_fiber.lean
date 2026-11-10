-- Prove2me | solution 1 for OAI.CompletedGauss.completed_reflected_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T15:20:31.079828+00:00
-- url     : https://prove2.me/submissions/caff6a31-df0d-4386-bd5a-c2370dc2207c

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_ReflectedDyadicSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CompletedGauss_completed_actual_fiber_cost
import Theorems.Thm_OAI_CompletedGauss_completed_reflected_branch_series
import Theorems.Thm_OAI_CompletedGauss_reflectionExtractedDivisor_ne_zero
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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
namespace OAI.CompletedGauss
theorem _root_.solution
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K X : ℝ,1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i),
      Pairwise (fun i j => IsCoprime (P i) (P j)) →
      (∀i,P i∣I*Q) → (∀i,¬P i∣rowResidualPart I Q) →
    ∀e : ι→Fin 3,∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀J∈S i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀J∈T i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ,(∀i k,‖σ i k‖≤1) →
      (∑k : idealRange (completedResidualScale K I Q),‖∑'i : ℕ×ℕ×ℕ,
        reflectedBranchBlock P hg (fun i => completedLocalExponent I F (P i)) e W
          (completedResidualScale K I Q) (completedBranchScale K X I F Q P e) ρ q S T η σ i k‖^2)
        ≤C*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨C,hC,h⟩ := completed_reflected_branch_series W a b ha hsupp hW deltaLoss ρ q hδ hρ hq
  refine ⟨C,hC,?_⟩
  intro K X hK hX I F Q hI hQ hIK hscale ι _ P _ hg hcop hpool hres e S T hS hT η hη σ hσ
  have hn (J : Ideal O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj (v : Fin 3) := hn _
    (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i))
      (fun i => completedLocalExponent I F (P i)) e v)
  have hp := hn (∏i,P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i)))
  have hy : 0<completedBranchScale K X I F Q P e := by
    unfold completedBranchScale
    have hk : 0<completedResidualScale K I Q := by linarith
    have hx : 0<X := by linarith
    have hd := hj 1
    have he := hj 2
    positivity
  have hb := (h (completedResidualScale K I Q) (completedBranchScale K X I F Q P e)
    hscale hy P hg (fun i => completedLocalExponent I F (P i)) e S T hS hT η hη σ hσ).2
  have hc := completed_actual_fiber_cost deltaLoss K X hδ.le hK hX I F Q hI hQ hIK P hcop hpool hres e
  have hm := mul_le_mul_of_nonneg_left hc hC.le
  apply hb.trans
  convert hm using 1 <;> (try dsimp [completedResidualScale,completedBranchScale]) <;> ring
end OAI.CompletedGauss
