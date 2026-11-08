-- Prove2me | solution 1 for OAI.TruncatedPrincipalPoisson.middle_divisor_frequency_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:26:50.616421+00:00
-- url     : https://prove2.me/submissions/f186697f-5853-4fd1-9e49-e5c60a257038

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_PrimitiveRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_PrincipalTruncation
import Theorems.Thm_OAI_TruncatedPrincipalPoisson_dualFar_decay
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
import Theorems.Thm_OAI_TruncatedPrincipalPoisson_subsetMobius_norm_le_one
import Theorems.Thm_OAI_TruncatedPrincipalPoisson_subsetNorm_pos
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
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.TruncatedPrincipalPoisson
theorem _root_.solution (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ),
        0 < X → 0 < Y → Y ≤ Z → 0 ≤ lengthScale →
        ‖(X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
          (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale‖ ≤
          (2 : ℝ) ^ S.card * (X / Y) * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := dualFar_decay A
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Y Z lengthScale hX hY hYZ hL
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let Q := (min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 0 < Z := hY.trans_le hYZ
  have hQ : 0 < Q := by dsimp [Q]; positivity
  rw [Finset.mul_sum]
  have hf (E : Finset ι) (hE : E ∈ middleDivisors P S Y Z) :
      ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) *
        dualFar W (X / subsetNorm P E) lengthScale)‖ ≤ (X / Y) * (B / Q) := by
    have hn := subsetNorm_pos P E
    have hEY : Y < subsetNorm P E := (Finset.mem_filter.mp hE).2
    have hEZ : subsetNorm P E ≤ Z := (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).2
    have hk : X / Z ≤ X / subsetNorm P E := div_le_div_of_nonneg_left hX.le hn hEZ
    have hden : Q ≤ (min 1 (X / subsetNorm P E)) ^ 2 *
        (1 + (X / subsetNorm P E) * lengthScale) ^ A := by
      dsimp [Q]
      have hmul : X * lengthScale / Z ≤ (X / subsetNorm P E) * lengthScale := by
        calc
          _ = (X / Z) * lengthScale := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hk hL
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) (min_le_min_left _ hk) 2
      · exact pow_le_pow_left₀ (by positivity) (by linarith) A
      · positivity
      · positivity
    have hh : ‖dualFar W (X / subsetNorm P E) lengthScale‖ ≤ B / Q :=
      (hb W _ lengthScale (div_pos hX hn) hL).trans (div_le_div_of_nonneg_left hB hQ hden)
    calc
      _ = (X / subsetNorm P E) * ‖subsetMobius P E‖ * ‖dualFar W (X / subsetNorm P E) lengthScale‖ := by
        simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hX, abs_of_pos hn]
        ring
      _ ≤ (X / Y) * 1 * (B / Q) := by
        apply mul_le_mul
        · exact mul_le_mul (div_le_div_of_nonneg_left hX.le hY hEY.le)
            (subsetMobius_norm_le_one P E) (norm_nonneg _) (by positivity)
        · exact hh
        · exact norm_nonneg _
        · positivity
      _ = _ := by ring
  calc
    _ ≤ ∑ E ∈ middleDivisors P S Y Z,
        ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale)‖ := norm_sum_le _ _
    _ ≤ ∑ E ∈ middleDivisors P S Y Z, (X / Y) * (B / Q) := Finset.sum_le_sum hf
    _ = ((middleDivisors P S Y Z).card : ℝ) * ((X / Y) * (B / Q)) := by simp
    _ ≤ (2 : ℝ) ^ S.card * ((X / Y) * (B / Q)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hsub : middleDivisors P S Y Z ⊆ S.powerset :=
        (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_powerset] at hc
      exact_mod_cast hc
    _ = _ := by dsimp [B, Q]; ring
end OAI.TruncatedPrincipalPoisson
