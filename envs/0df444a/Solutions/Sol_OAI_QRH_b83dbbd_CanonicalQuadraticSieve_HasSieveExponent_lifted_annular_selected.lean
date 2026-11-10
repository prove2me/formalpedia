-- Prove2me | solution 1 for OAI.QRH_b83dbbd.CanonicalQuadraticSieve.HasSieveExponent.lifted_annular_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:35:28.317222+00:00
-- url     : https://prove2.me/submissions/c282e103-cc8e-46b7-af22-b3a107c1a86f

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
import Theorems.Thm_OAI_CanonicalQuadraticSieve_lifting_annular_scale_bounds
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_annularHighEnergy_coefficientAtScale
import Theorems.Thm_OAI_CanonicalQuadraticSieve_coefficientAtScale_energy
import Theorems.Thm_OAI_CanonicalQuadraticSieve_coefficientAtScale_shell
import Theorems.Thm_OAI_CanonicalQuadraticSieve_cutoffRescaleCoefficient_bounds
import Theorems.Thm_OAI_CanonicalQuadraticSieve_fixedCutoffBase_bounds
import Theorems.Thm_OAI_CanonicalQuadraticSieve_selectedPoissonK_rescale
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
import Theorems.Thm_OAI_QRH_b83dbbd_CanonicalQuadraticSieve_HasSieveExponent_annular_selected_bound
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
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
namespace OAI.CanonicalQuadraticSieve
namespace HasSieveExponent
theorem _root_.solution {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) :
    ∃ C : ℝ, 0<C ∧ ∀ (M N : ℝ),
      1≤M → 28≤N → N^(2-1/α)≤M →
      1≤selectedPoissonK fixedCutoffBase M N η →
      ∀ (j : Fin 7) (q : ℝ), 1≤q → q≤7 →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N (N/q) a →
      annularHighEnergy ((2:ℝ)^j.val*M) N (selectedPoissonK fixedCutoffBase M N η) a ≤
        C*(M*N)^(260*η)*M*∑J,‖a J‖^2 := by
  have hc0 : 0<fixedCutoffBase := lt_of_lt_of_le (by norm_num) fixedCutoffBase_bounds.1
  obtain ⟨C,hC,hann⟩ := hexp.annular_selected_bound hα1 hα2 η hη hη1 l A hl hA
    (21952*fixedCutoffBase) (by linarith [fixedCutoffBase_bounds.1])
  refine ⟨C*64^(260*η)*64,by positivity,?_⟩
  intro M N hM hN hthreshold hK j q hq hq7 a ha
  let r : ℝ := (2:ℝ)^j.val
  have hr := lifting_annular_scale_bounds j
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hq0 : 0<q := by linarith
  have hr0 : 0<r := by dsimp [r]; positivity
  have hNq : 4≤N/q := (le_div_iff₀ hq0).mpr (by nlinarith)
  have hNqN : N/q≤N := div_le_self hN0.le hq
  have hβ : 0≤2-1/α := by
    have hfrac : 1/α≤1 := (div_le_one (by linarith : 0<α)).mpr hα1
    linarith
  have hth : (N/q)^(2-1/α)≤r*M := by
    calc
      _ ≤ N^(2-1/α) := Real.rpow_le_rpow (by positivity) hNqN hβ
      _ ≤ M := hthreshold
      _ ≤ r*M := by nlinarith [hr.1]
  let c := cutoffRescaleCoefficient fixedCutoffBase η r q
  have hc := cutoffRescaleCoefficient_bounds fixedCutoffBase η r q hc0.le hη.le hη1 hr.1 hr.2 hq hq7
  have hk := selectedPoissonK_rescale fixedCutoffBase M N η r q hM0 hN0 hr0 hq0
  have hh := hann c (r*M) (N/q) hc.1 hc.2 (by nlinarith [hr.1]) hNq hth
    (by simpa only [c,hk] using hK) (coefficientAtScale N (N/q) a)
    (coefficientAtScale_shell N (N/q) a ha)
  dsimp only [c] at hh
  rw [hk,←annularHighEnergy_coefficientAtScale (r*M) N (N/q)
    (selectedPoissonK fixedCutoffBase M N η) a (fun J hJ => (ha J hJ).2),
    ←coefficientAtScale_energy N (N/q) a (fun J hJ => (ha J hJ).2)] at hh
  have hp : ((r*M)*(N/q))^(260*η)≤64^(260*η)*(M*N)^(260*η) := by
    calc
      _ ≤ (64*(M*N))^(260*η) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        calc
          (r*M)*(N/q) ≤ (64*M)*N := by gcongr; exact hr.2
          _ = _ := by ring
      _ = _ := Real.mul_rpow (by norm_num) (by positivity)
  change annularHighEnergy (r*M) N _ a≤_
  apply hh.trans
  calc
    _ ≤ C*(64^(260*η)*(M*N)^(260*η))*(64*M)*∑J,‖a J‖^2 := by
      gcongr
      exact hr.2
    _ = _ := by ring
end HasSieveExponent
end OAI.CanonicalQuadraticSieve
