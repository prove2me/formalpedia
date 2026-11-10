-- Prove2me | solution 1 for OAI.CompletedGauss.ReflectedFiberData.energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:49:24.193611+00:00
-- url     : https://prove2.me/submissions/724673b5-7963-41bf-aa84-668a44de6d65

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
import Theorems.Thm_OAI_CompletedGauss_ReflectedBranchData_energy_bound
import Theorems.Thm_OAI_CompletedGauss_ReflectedFiberData_finite_energy_bound
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_energy_bound
import Theorems.Thm_OAI_CompletedGauss_completed_branch_count_small_power
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
import Theorems.Thm_OAI_FiniteSieveOperator_energy_bound
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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve
open OAI.CompletedGauss.ReflectedFiberData
namespace OAI.CompletedGauss.ReflectedFiberData
theorem _root_.solution
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀(rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q → ∀d : ReflectedFiberData rays levelBound K I F Q,
      (∑k,‖d.value W X ρ q k‖^2)≤
        C*(rays:ℝ)^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨Cb,hCb,hb⟩ := ReflectedBranchData.energy_bound W a b ha hsupp hW deltaLoss ρ q levelBound hδ hρ hq hlevel
  obtain ⟨Cp,hCp,hp⟩ := completed_branch_count_small_power ε hε
  refine ⟨Cb*Cp,by positivity,?_⟩
  intro rays K X hK hX I F Q hI hQ hIK hk d
  let : ∀p : d.pool,p.val.IsMaximal := d.maximal
  have hcount := hp (I*Q) (mul_ne_zero hI hQ) (fun p : d.pool => p.val)
    Subtype.val_injective d.divides
  have hnorm : (Ideal.absNorm (I*Q):ℝ)≤K*(Ideal.absNorm Q:ℝ) := by
    simp only [map_mul,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hIK (Nat.cast_nonneg _)
  have hcount' : (6:ℝ)^(2*d.pool.card)≤Cp*(K*(Ideal.absNorm Q:ℝ))^ε := by
    have hc : (6:ℝ)^(2*d.pool.card)≤Cp*(Ideal.absNorm (I*Q):ℝ)^ε := by
      simpa only [Fintype.card_coe] using hcount
    exact hc.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hε.le) hCp.le)
  have he := finite_energy_bound
    (fun b => (d.branch b).value W X ρ q) d.weight d.weight_bound _
    (fun b => hb K X hK hX I F Q hI hQ hIK hk (d.branch b))
  change (∑k,‖d.value W X ρ q k‖^2)≤_ at he
  apply he.trans
  have hc : (Fintype.card (Fin rays×(d.pool→Fin 6)):ℝ)^2=(rays:ℝ)^2*(6:ℝ)^(2*d.pool.card) := by
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_mul,Nat.cast_pow]
    rw [mul_pow,←pow_mul,Nat.mul_comm d.pool.card 2]
    norm_num
  rw [hc]
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hKQ : 0<K*(Ideal.absNorm Q:ℝ) := mul_pos (by linarith) hnQ
  calc
    _ ≤ ((rays:ℝ)^2*(Cp*(K*(Ideal.absNorm Q:ℝ))^ε))*
      (Cb*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
        (Ideal.absNorm (rowPowerfulPart I):ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcount' (sq_nonneg _)
    _ = _ := by rw [Real.rpow_add hKQ]; ring
end OAI.CompletedGauss.ReflectedFiberData
