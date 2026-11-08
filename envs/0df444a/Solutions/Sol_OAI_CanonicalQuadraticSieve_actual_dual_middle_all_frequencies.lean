-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.actual_dual_middle_all_frequencies
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:00:25.674791+00:00
-- url     : https://prove2.me/submissions/28c5e882-849e-4950-806f-9c1e9fbde925

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SpatialDerivatives
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FirstCoreCutoff
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_LatticeEnvelopes
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_nonzero_lattice_envelope_sum
import Theorems.Thm_OAI_CanonicalQuadraticSieve_dualMiddleDecayConstant_nonneg
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisorBlockCost_mono_coefficients
import Theorems.Thm_OAI_CanonicalQuadraticSieve_dualMiddleAt_nonneg
import Theorems.Thm_OAI_CanonicalQuadraticSieve_dual_middle_scale_identity
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_principal_middle_prefactor_sum
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
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ≤
        (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) * (M / (F * N)) *
          Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀) := by
  let t := (N * Real.sqrt (F / (M * B))) / (D₁ * D₂)
  let r := M / (F * N)
  have ht : 0 < t := by dsimp only [t]; positivity
  have hr0 : 0 < r := by dsimp only [r]; positivity
  let C := dualMiddleDecayConstant W * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀)
  have hC : 0 ≤ C := mul_nonneg (dualMiddleDecayConstant_nonneg W) (Real.sqrt_nonneg _)
  have hpoint (h : {h : O // h ≠ 0}) :
      (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 *
        dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val ≤ (2 * t * r) * C := by
    have hk := (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.2 ε hε S T D₁ D₂ B N M F
      hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright (a h.val) (b h.val) h.val h.property
    change _ ≤ dualMiddleDecayConstant W *
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N (a h.val) (b h.val)) at hk
    have hcost := divisorBlockCost_mono_coefficients ε hε D₁ D₂ B N
      (by linarith) (by linarith) (a h.val) a₀ (b h.val) b₀ (ha h.val) (hb h.val)
    have hk' := hk.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcost)
      (dualMiddleDecayConstant_nonneg W))
    have hp := principal_middle_prefactor_sum S T rows
      (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right (a h.val) (b h.val) D.val E.val i j k *
        paperRadialFourier W (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h.val‖ ^ 2 /
            ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖)
      (fun _ _ _ => norm_nonneg _) (M / F) B D₁ D₂ (div_pos hM hF) (by linarith) (by linarith) (by linarith)
      (fun i => (hrows i).2.1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
    have harg : N * Real.sqrt (F / (M * B)) * ‖eisEmbedding h.val‖ ^ 2 / (D₁ * D₂) =
        t * ‖eisEmbedding h.val‖ ^ 2 := by dsimp only [t]; ring
    rw [harg] at hk'
    have hpre : 2 * Real.sqrt ((M / F) / B) / (D₁ * D₂) = 2 * t * r := by
      rw [dual_middle_scale_identity M F B N hM hF (by linarith) (by linarith)]
      dsimp only [t, r]
      ring
    rw [hpre] at hp
    change dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val ≤ _ at hp
    calc
      _ ≤ (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * ((2 * t * r) * _) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = (2 * t * r) * ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * _) := by ring
      _ ≤ (2 * t * r) * C := mul_le_mul_of_nonneg_left hk' (by positivity)
  obtain ⟨hs, hv⟩ := nonzero_lattice_envelope_sum t ((2 * t * r) * C) ht (by positivity)
    _ (fun h => dualMiddleAt_nonneg W S T rows left right (a h.val) (b h.val) M F h.val) hpoint
  refine ⟨hs, (mul_le_mul_iff_right₀ ht).mp ?_⟩
  calc
    _ ≤ nonzeroLatticeEnvelopeConstant * ((2 * t * r) * C) := hv
    _ = _ := by dsimp only [C, r]; ring
end OAI.CanonicalQuadraticSieve
