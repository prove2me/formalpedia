-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.HasSieveExponent.original_middle_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:27:06.247222+00:00
-- url     : https://prove2.me/submissions/419fce74-16c9-48ca-a666-0858928fe54a

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SupportNorms
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MiddleWindows
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_original_middle_window
import Theorems.Thm_OAI_CanonicalQuadraticSieve_originalMiddleWindowAt_dyadic
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisorDyadicBin_bounds
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisorDyadicBin_scale_le
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisorDyadicScale_ge_one
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisorEnergyFactor_nonneg
import Theorems.Thm_OAI_CanonicalQuadraticSieve_divisorExponentConstant_pos
import Theorems.Thm_OAI_CanonicalQuadraticSieve_originalMiddleDecayConstant_nonneg
import Theorems.Thm_OAI_CanonicalQuadraticSieve_originalMiddleWindowAt_eq_zero
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_nonzeroLatticeEnvelopeConstant_nonneg
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
open OAI.CanonicalQuadraticSieve
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
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
namespace OAI.CanonicalQuadraticSieve
namespace HasSieveExponent
theorem _root_.solution {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (S T : Finset (Ideal O)) (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ N)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))) := by
  classical
  let V := (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))
  have hV : 0 ≤ V := by
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := originalMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    dsimp only [V]
    positivity
  let f := fun (j k : Fin (columnDyadicLength N + 1)) (h : {h : O // h ≠ 0}) =>
    originalMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      rows left right (a h.val) (b h.val) M P h.val
  have hf (j k : Fin (columnDyadicLength N + 1)) : Summable (f j k) ∧ (∑' h, f j k h) ≤ V := by
    by_cases hSj : (divisorDyadicBin S N j).Nonempty
    · by_cases hTk : (divisorDyadicBin T N k).Nonempty
      · exact hexp.original_middle_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M U
          (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN
          (divisorDyadicBin_scale_le S N hS j hSj) (divisorDyadicBin_scale_le T N hT k hTk)
          hM (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
          rows left right hr hl hri hrows a₀ b₀ a b ha hb hU W P hleft hright
          (fun D E i hp => hP
            ⟨D.val, (Finset.mem_filter.mp D.property).1⟩
            ⟨E.val, (Finset.mem_filter.mp E.property).1⟩ i hp)
      · have hz := Finset.not_nonempty_iff_eq_empty.mp hTk
        have he : f j k = fun _ => 0 := by
          funext h
          apply originalMiddleWindowAt_eq_zero
          intro D E i hp
          have hh := E.property
          simp only [hz, Finset.notMem_empty] at hh
        rw [he]
        simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hSj
      have he : f j k = fun _ => 0 := by
        funext h
        apply originalMiddleWindowAt_eq_zero
        intro D E i hp
        have hh := D.property
        simp only [hz, Finset.notMem_empty] at hh
      rw [he]
      simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
  have he : (fun h : {h : O // h ≠ 0} =>
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) =
      fun h => ∑ j, ∑ k, f j k h := by
    funext h
    exact originalMiddleWindowAt_dyadic W S T N rows left right (a h.val) (b h.val) M P h.val
  rw [he]
  refine ⟨summable_sum (fun j _ => summable_sum (fun k _ => (hf j k).1)), ?_⟩
  rw [Summable.tsum_finsetSum (fun j _ => summable_sum (fun k _ => (hf j k).1))]
  calc
    _ = ∑ j, ∑ k, ∑' h, f j k h := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Summable.tsum_finsetSum (fun k _ => (hf j k).1)
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), V :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => (hf j k).2))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, V, pow_two]; ring
end HasSieveExponent
end OAI.CanonicalQuadraticSieve
