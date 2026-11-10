-- Prove2me | solution 1 for OAI.CompletedGauss.completed_mean_square_of_exact_reflection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:56:53.250197+00:00
-- url     : https://prove2.me/submissions/c993932f-814f-45c4-967a-20c6e6bdb185

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
import Theorems.Thm_OAI_CompletedGauss_completedRowDyad_bounds
import Theorems.Thm_OAI_CompletedGauss_completedRowDyad_sum
import Theorems.Thm_OAI_CompletedGauss_completedRowDyadic_shape
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CompletedGauss_completed_energy_of_exact_models
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
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic
open ActualEisensteinCubic CanonicalQuadraticSieve
namespace OAI.CompletedGauss
theorem _root_.solution
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀(rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal O)) (F Q : Ideal O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal O→O→*ℂ) (lengthScale : ℂ),HasExactCompletedDyadicModels rays rows K X ρ q levelBound F Q W Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) W X‖^2)≤
        C*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
          (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  let deltaLoss : ℝ := ε/12
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨C,hC,h⟩ := completed_energy_of_exact_models W a b ha hsupp hW deltaLoss deltaLoss ρ q levelBound hδ hδ hρ hq hlevel
  let s : ℝ := 10*deltaLoss+deltaLoss
  have hs : 0≤s := by dsimp [s]; positivity
  refine ⟨C*(16*(2:ℝ)^s),by positivity,?_⟩
  intro rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hmodels
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  let A : ℝ := C*(rays:ℝ)^2*‖lengthScale‖^2*(Ideal.absNorm Q:ℝ)^deltaLoss
  have hA : 0≤A := by dsimp [A]; positivity
  rw [←completedRowDyad_sum rows K (by linarith : 0≤K) (fun I hI => (hrows I hI).2)
    (fun I => ‖completedT (Ψ I) W X‖^2)]
  have hper (j : ℕ) (hj : j∈Finset.range (completedRowDyadicLength K+1)) :
      (∑I∈completedRowDyad rows j,‖completedT (Ψ I) W X‖^2)≤
        A*(((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
          ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X)) := by
    have hb := h rays ((2:ℝ)^j) X (one_le_pow₀ (by norm_num)) hX
      (completedRowDyad rows j) F Q hQ hbad
      (fun I hI => ⟨(completedRowDyad_bounds rows j (fun I hI => (hrows I hI).1) I hI).1,
        (completedRowDyad_bounds rows j (fun I hI => (hrows I hI).1) I hI).2.2⟩)
      Ψ lengthScale (hmodels j hj)
    convert hb using 1
    dsimp [A,s]
    ring
  calc
    _ ≤ ∑j∈Finset.range (completedRowDyadicLength K+1),
      A*(((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
        ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X)) := Finset.sum_le_sum hper
    _ = A*∑j∈Finset.range (completedRowDyadicLength K+1),
      ((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
        ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*((16*(2:ℝ)^s)*(K*(Ideal.absNorm Q:ℝ))^s*(K+K^2*(Ideal.absNorm Q:ℝ)/X)) :=
      mul_le_mul_of_nonneg_left (completedRowDyadic_shape s K X (Ideal.absNorm Q:ℝ) hs hK
        (by linarith) hnQ) hA
    _ ≤ (C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
        (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
      have hnq : (Ideal.absNorm Q:ℝ)^deltaLoss≤(K*(Ideal.absNorm Q:ℝ))^deltaLoss := by
        apply Real.rpow_le_rpow hnQ.le _ hδ.le
        exact le_mul_of_one_le_left hnQ.le hK
      have hpower : (Ideal.absNorm Q:ℝ)^deltaLoss*(K*(Ideal.absNorm Q:ℝ))^s≤
          (K*(Ideal.absNorm Q:ℝ))^ε := by
        apply (mul_le_mul_of_nonneg_right hnq (by positivity)).trans_eq
        rw [←Real.rpow_add (mul_pos (by linarith) hnQ)]
        congr 1
        dsimp [s,deltaLoss]
        ring
      calc
        _ = ((C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K+K^2*(Ideal.absNorm Q:ℝ)/X))*
          ((Ideal.absNorm Q:ℝ)^deltaLoss*(K*(Ideal.absNorm Q:ℝ))^s) := by dsimp [A]; ring
        _ ≤ ((C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K+K^2*(Ideal.absNorm Q:ℝ)/X))*
          (K*(Ideal.absNorm Q:ℝ))^ε := mul_le_mul_of_nonneg_left hpower (by positivity)
        _ = _ := by ring
end OAI.CompletedGauss
