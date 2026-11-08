-- Prove2me | solution 1 for OAI.TruncatedPrincipalPoisson.small_divisor_dual_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:25:49.920735+00:00
-- url     : https://prove2.me/submissions/ad2da051-c940-40c6-921c-1b020d2694de

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_Rows
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_PrimitiveRows
import Theorems.Thm_OAI_TruncatedPrincipalPoisson_subsetNorm_pos
import Theorems.Thm_OAI_TruncatedPrincipalPoisson_radialDual_decay
import Theorems.Thm_OAI_TruncatedPrincipalPoisson_subsetMobius_norm_le_one
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


section
namespace OAI
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
namespace CubicEisenstein
open scoped BigOperators Classical MatrixGroups Matrix
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
end CubicEisenstein
open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson
section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
end
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
end TruncatedPrincipalPoisson
namespace EisensteinSchwartzPoisson
open ConcreteTraceCRT
end EisensteinSchwartzPoisson
open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
private theorem scale_tail_bound (A : ℕ) (B x Y X : ℝ)
    (hB : 0 ≤ B) (hx : 0 < x) (hxY : x ≤ Y) (hX : 0 < X) :
    (X / x) * (B / (1 + X / x) ^ (A + 1)) ≤ B * (Y / X) ^ A := by
  have hu : 0 < X / x := div_pos hX hx
  calc
    _ ≤ (X / x) * (B / (X / x) ^ (A + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hu.le
      exact div_le_div_of_nonneg_left hB (pow_pos hu _) (pow_le_pow_left₀ hu.le (by linarith) _)
    _ = B * (x / X) ^ A := by
      simp only [div_pow, pow_succ]
      field_simp

    _ ≤ B * (Y / X) ^ A := by gcongr
private theorem norm_sum_subsets_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (T : Finset (Finset ι)) (hT : T ⊆ S.powerset) (f : Finset ι → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ E ∈ T, ‖f E‖ ≤ B) :
    ‖∑ E ∈ T, f E‖ ≤ (2 : ℝ) ^ S.card * B := by
  calc
    _ ≤ ∑ E ∈ T, ‖f E‖ := norm_sum_le _ _
    _ ≤ ∑ E ∈ T, B := Finset.sum_le_sum hf
    _ = (T.card : ℝ) * B := by simp
    _ ≤ (2 : ℝ) ^ S.card * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      have hc := Finset.card_le_card hT
      rw [Finset.card_powerset] at hc
      exact_mod_cast hc
end TruncatedPrincipalPoisson
end
end OAI
end

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
open scoped BigOperators Classical SchwartzMap
open OAI.TruncatedPrincipalPoisson
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.TruncatedPrincipalPoisson
theorem _root_.solution (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y : ℝ), 0 < X → 0 ≤ Y → Y ≤ X →
        ‖(X : ℂ) * ∑ E ∈ smallDivisors P S Y,
          (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * (Y / X) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := radialDual_decay (A + 1)
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Y hX hY hYX
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  rw [Finset.mul_sum]
  have hf (E : Finset ι) (hE : E ∈ smallDivisors P S Y) :
      ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) *
        radialDual W (X / subsetNorm P E))‖ ≤ B * (Y / X) ^ A := by
    have hn := subsetNorm_pos P E
    have hEY : subsetNorm P E ≤ Y := (Finset.mem_filter.mp hE).2
    have hscale : 1 ≤ X / subsetNorm P E := (le_div_iff₀ hn).mpr (by simpa using hEY.trans hYX)
    calc
      _ = (X / subsetNorm P E) * ‖subsetMobius P E‖ * ‖radialDual W (X / subsetNorm P E)‖ := by
        simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hX, abs_of_pos hn]
        ring
      _ ≤ (X / subsetNorm P E) * 1 * (B / (1 + X / subsetNorm P E) ^ (A + 1)) := by
        gcongr
        · exact subsetMobius_norm_le_one P E
        · exact hb W _ hscale
      _ ≤ B * (Y / X) ^ A := by
        simpa only [mul_one] using scale_tail_bound A B (subsetNorm P E) Y X hB hn hEY hX
  exact (norm_sum_subsets_le S _ (Finset.filter_subset _ _) _ _ (by positivity) hf).trans_eq (by ring)
end OAI.TruncatedPrincipalPoisson
