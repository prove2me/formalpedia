-- Prove2me | solution 1 for OAI.TruncatedPrincipalPoisson.truncationError_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:43:20.523853+00:00
-- url     : https://prove2.me/submissions/50b704f8-fb63-4292-839b-6055580dc347

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_PrimitiveRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_PrincipalTruncation
import Theorems.Thm_OAI_TruncatedPrincipalPoisson_middle_divisor_frequency_tail
import Theorems.Thm_OAI_TruncatedPrincipalPoisson_truncationError_eq
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
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
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_TruncatedPrincipalPoisson_large_divisor_source_tail
import Theorems.Thm_OAI_TruncatedPrincipalPoisson_small_divisor_dual_tail
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
open scoped BigOperators Classical SchwartzMap
open OAI.TruncatedPrincipalPoisson
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
namespace OAI.TruncatedPrincipalPoisson
theorem _root_.solution (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ),
        0 < X → 0 < Y → Y ≤ X → X ≤ Z → 0 ≤ lengthScale →
        ‖truncationError P S W X Y Z lengthScale‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            ((Y / X) ^ A + (1 / (1 + Z / X) ^ A) +
              (X / Y) / ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A)) := by
  obtain ⟨s₀, C₀, hC₀, h₀⟩ := small_divisor_dual_tail A
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := large_divisor_source_tail A
  obtain ⟨s₂, C₂, hC₂, h₂⟩ := middle_divisor_frequency_tail A
  refine ⟨(s₀ ∪ s₁) ∪ s₂, C₀ + C₁ + C₂, by positivity, ?_⟩
  intro ι _ P _ hinj S W X Y Z lengthScale hX hY hYX hXZ hL
  let Q := ((s₀ ∪ s₁) ∪ s₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let C := C₀ + C₁ + C₂
  have hQ : 0 ≤ Q := apply_nonneg _ _
  have hc₀ : C₀ ≤ C := by dsimp [C]; linarith
  have hc₁ : C₁ ≤ C := by dsimp [C]; linarith
  have hc₂ : C₂ ≤ C := by dsimp [C]; linarith
  have hq₀ : s₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left.trans Finset.subset_union_left)) W
  have hq₁ : s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right.trans Finset.subset_union_left)) W
  have hq₂ : s₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W
  have hz : 0 < Z := hX.trans_le hXZ
  let lo : ℂ := (X : ℂ) * ∑ E ∈ smallDivisors P S Y,
    (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)
  let mid : ℂ := (X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
    (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale
  let hi : ℂ := ∑ E ∈ largeDivisors P S Z,
    subsetMobius P E * radialSource W (X / subsetNorm P E)
  have hlo : ‖lo‖ ≤ (2 : ℝ) ^ S.card * (C * Q) * (Y / X) ^ A := by
    apply (h₀ P S W X Y hX hY.le hYX).trans
    gcongr
  have hhi : ‖hi‖ ≤ (2 : ℝ) ^ S.card * (C * Q) / (1 + Z / X) ^ A := by
    apply (h₁ P S W X Z hX hXZ).trans
    gcongr
  have hmid : ‖mid‖ ≤ (2 : ℝ) ^ S.card * (X / Y) * (C * Q) /
      ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) := by
    apply (h₂ P S W X Y Z lengthScale hX hY (hYX.trans hXZ) hL).trans
    gcongr
  rw [truncationError_eq P hinj S W X Y Z lengthScale hX (hYX.trans hXZ) hL]
  change ‖lo + mid + hi‖ ≤ _
  calc
    _ ≤ ‖lo‖ + ‖mid‖ + ‖hi‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le lo mid) le_rfl)
    _ ≤ (2 : ℝ) ^ S.card * (C * Q) * (Y / X) ^ A +
        (2 : ℝ) ^ S.card * (X / Y) * (C * Q) / ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) +
        (2 : ℝ) ^ S.card * (C * Q) / (1 + Z / X) ^ A := add_le_add (add_le_add hlo hmid) hhi
    _ = _ := by change _ = (2 : ℝ) ^ S.card * (C * Q) * _; ring
end OAI.TruncatedPrincipalPoisson
