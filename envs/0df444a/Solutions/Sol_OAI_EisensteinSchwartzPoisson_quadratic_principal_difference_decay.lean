-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.quadratic_principal_difference_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:49:59.895397+00:00
-- url     : https://prove2.me/submissions/0550bc11-7ae0-41ba-a968-20b955c41e8e

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_KernelEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_quadratic_principal_difference_large_scale
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_quadratic_principal_difference_uniform
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_two_regime_decay
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_ne_zero
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_norm_sq
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply



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
open scoped BigOperators Classical SchwartzMap FourierTransform
open OAI.EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT
open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
          (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            (1 + M / (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)) ^ A := by
  obtain ⟨s₀, C₀, hC₀, h₀⟩ := quadratic_principal_difference_uniform
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := quadratic_principal_difference_large_scale A
  refine ⟨s₀ ∪ s₁, (2 : ℝ) ^ A * (C₀ + C₁), by positivity, ?_⟩
  intro α _ P _ hinj S W M hM
  let N := (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)
  let Q := (s₀ ∪ s₁).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let d := (2 : ℝ) ^ S.card
  let deltaLoss := ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
    (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖
  have hN : 0 < N := by
    dsimp [N]
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P S)))
  have hQ : 0 ≤ Q := apply_nonneg _ _
  have hd : 0 ≤ d := by positivity
  have hq₀ : s₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) W
  have hq₁ : s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W
  have hb₀ : deltaLoss ≤ d * (C₀ * Q) := by
    apply (h₀ P hinj S W M hM).trans
    dsimp only [d]
    gcongr
  have hb₁ : N ≤ M → deltaLoss ≤ d * (C₁ * Q) * (N / M) ^ A := by
    intro hsize
    apply (h₁ P hinj S W M hM hsize).trans
    dsimp only [d, N]
    gcongr
  have h := two_regime_decay A deltaLoss (d * (C₀ * Q)) (d * (C₁ * Q)) M N
    (norm_nonneg _) (by positivity) (by positivity) hM hN hb₀ hb₁
  calc
    _ = deltaLoss := rfl
    _ ≤ (2 : ℝ) ^ A * (d * (C₀ * Q) + d * (C₁ * Q)) / (1 + M / N) ^ A := h
    _ = _ := by dsimp [d, N, Q]; ring
end OAI.EisensteinSchwartzPoisson
