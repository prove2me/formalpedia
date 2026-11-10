-- Prove2me | solution 1 for OAI.QRH_b83dbbd.CanonicalQuadraticSieve.HasSieveExponent.annular_selected_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:31:32.553828+00:00
-- url     : https://prove2.me/submissions/1c8f11b7-b5e4-4c65-bb2c-3c385f79b2ff

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonConstants
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Theorems.Thm_OAI_CanonicalQuadraticSieve_improved_threshold_shape
import Theorems.Thm_OAI_CanonicalQuadraticSieve_fixedBadNorm_one_le
import Theorems.Thm_OAI_CanonicalQuadraticSieve_fixedCutoffBase_bounds
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_annular_energy_from_scalar_cost
import Theorems.Thm_OAI_CanonicalQuadraticSieve_chosen_large_gcd_full
import Theorems.Thm_OAI_CanonicalQuadraticSieve_commonMaskIdeal_norm
import Theorems.Thm_OAI_CanonicalQuadraticSieve_commonMaskIdeal_squarefree
import Theorems.Thm_OAI_CanonicalQuadraticSieve_gcdPool_admissible
import Theorems.Thm_OAI_CanonicalQuadraticSieve_largeGcdThreshold_bounds
import Theorems.Thm_OAI_CanonicalQuadraticSieve_poissonComparisonMajorant_selected_power
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_DivisorBlockCauchy_divisorConstant_pos
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
open scoped BigOperators Classical SchwartzMap
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy
namespace OAI.CanonicalQuadraticSieve
namespace HasSieveExponent
theorem _root_.solution {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) (C1 : ℝ) (hC1 : 1≤C1) :
    ∃ C : ℝ, 0<C ∧ ∀ (c M N : ℝ),
      fixedCutoffBase≤c → c≤C1 → 1≤M → 4≤N → N^(2-1/α)≤M →
      1≤selectedPoissonK c M N η →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N (selectedPoissonK c M N η) a ≤
        C*(M*N)^(260*η)*M*∑J,‖a J‖^2 := by
  have hα : 1/2≤α := by linarith
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,CH,hCD,hCS,hCT,hCP,hCH,henergy⟩ :=
    hexp.annular_energy_from_scalar_cost hα η hη l A
  obtain ⟨CF,hCF,hscalar⟩ := poissonComparisonMajorant_selected_power hexp hα hα2
    η hη hη1 l A hl hA sD sS sT CD CS CT CP hCD.le hCS.le hCT.le hCP.le
    fixedBadNorm C1 fixedBadNorm_one_le hC1 QuadraticInitialBound.annularSieveCutoff
  have hdiv : 0<divisorConstant η hη := divisorConstant_pos η hη
  let SD := supportConstant η hη*divisorConstant η hη
  have hSD : 0<SD := mul_pos (supportConstant_pos η hη) (divisorConstant_pos η hη)
  let F := 16*(3*CF*divisorConstant η hη + 4*CH*2^η*SD)
  refine ⟨F,by dsimp [F]; positivity,?_⟩
  intro c M N hc hc1 hM hN hthreshold hK a ha
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hN1 : 1≤N := by linarith
  have hP : 1≤M*N := by nlinarith
  have hP0 : 0<M*N := by positivity
  have hc4 : 4≤c := fixedCutoffBase_bounds.1.trans hc
  have hcB : fixedBadNorm≤c := fixedCutoffBase_bounds.2.trans hc
  have hT : 4≤selectedPoissonT c M N η := by
    have hp := Real.one_le_rpow hP hη.le
    unfold selectedPoissonT
    nlinarith
  have hcut : N^2/M≤selectedPoissonK c M N η := by
    unfold selectedPoissonK
    rw [mul_div_assoc]
    have hp : 0≤N^2/M := by positivity
    nlinarith
  have hH := largeGcdThreshold_bounds α N hα1 hα2 hN
  have hcost : ∀D∈gcdPool (fun J : idealRange N => J.val),
      (Ideal.absNorm D:ℝ)≤largeGcdThreshold α N →
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη
        (commonMaskIdeal D) (selectedPoissonK c M N η) (N/(Ideal.absNorm D:ℝ)) M
        (selectedPoissonT c M N η) (fun _ : Unit => (1:ℂ))
        QuadraticInitialBound.annularSieveCutoff ≤ 3*CF*(M*N)^(259*η)*M := by
    intro D hD hd
    have hadm := gcdPool_admissible (fun J : idealRange N => J.val)
      (fun J => (mem_idealRange.mp J.property).1) D hD
    have hd1 : 1≤(Ideal.absNorm D:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hadm.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hgn : (Ideal.absNorm (commonMaskIdeal D):ℝ)=fixedBadNorm*(Ideal.absNorm D:ℝ) := by
      rw [commonMaskIdeal_norm D hadm, Nat.cast_mul]
      rfl
    have hb := hscalar c M N (Ideal.absNorm D:ℝ) (commonMaskIdeal D) hc4 hcB hc1 hM hN1 hd1
      (by linarith [hH.2]) (commonMaskIdeal_squarefree D).ne_zero hgn hK
    apply hb.trans
    have hs : poissonShape M N α≤3*M := improved_threshold_shape α N M hα1 hN1 hthreshold
    calc
      _ ≤ CF*(M*N)^(259*η)*(3*M) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have he := henergy η hη M N (selectedPoissonK c M N η) (selectedPoissonT c M N η)
    (largeGcdThreshold α N) (3*CF*(M*N)^(259*η)*M) hM hN1 hK hT
    (by linarith [hH.1]) hH.2 (by positivity) hcost a ha
  have hhigh := chosen_large_gcd_full α η CH M N (selectedPoissonK c M N η)
    hα1 hα2 hη.le hCH.le hM0 hN (by linarith) hcut
  have hn : N^η≤(M*N)^η := Real.rpow_le_rpow hN0.le (by nlinarith) hη.le
  have hcombine1 : (M*N)^(259*η)*(M*N)^η=(M*N)^(260*η) := by
    rw [←Real.rpow_add hP0]
    congr 1
    ring
  have hcombine2 : (M*N)^η*((M*N)^η)^2=(M*N)^(3*η) := by
    rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
    congr 1
    ring
  have hpow : (M*N)^(3*η)≤(M*N)^(260*η) :=
    Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  have hfirst : (3*CF*(M*N)^(259*η)*M/6)*(divisorConstant η hη*N^η) ≤
      (3*CF*divisorConstant η hη)*(M*N)^(260*η)*M := by
    calc
      _ ≤ (3*CF*(M*N)^(259*η)*M)*(divisorConstant η hη*(M*N)^η) := by
        gcongr
        nlinarith [show 0≤3*CF*(M*N)^(259*η)*M by positivity]
      _ = _ := by rw [←hcombine1]; ring
  have hsecond : (CH*((2*M)*(N/largeGcdThreshold α N))^η*
      (2*M+Real.sqrt ((2*M)/selectedPoissonK c M N η)*(N/largeGcdThreshold α N)^α))*
      SD*(N^η)^2 ≤ (4*CH*2^η*SD)*(M*N)^(260*η)*M := by
    calc
      _ ≤ ((4*CH*2^η)*(M*N)^η*M)*SD*((M*N)^η)^2 := by gcongr
      _ = (4*CH*2^η*SD)*(M*N)^(3*η)*M := by rw [←hcombine2]; ring
      _ ≤ _ := by gcongr
  apply he.trans
  change 16*(_+_*SD*(N^η)^2)*_≤_
  calc
    _ ≤ 16*((3*CF*divisorConstant η hη)*(M*N)^(260*η)*M+
      (4*CH*2^η*SD)*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by dsimp [F]; ring
end HasSieveExponent
end OAI.CanonicalQuadraticSieve
