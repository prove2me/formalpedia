-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.maskedPrincipalRemainder_large_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:24:57.602289+00:00
-- url     : https://prove2.me/submissions/e2db6c12-a569-4c0f-95c6-149f964ee4b5

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_nonzero_sum_decay
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_principal_tail_scalar
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
import Theorems.Thm_OAI_QuadraticInitialBound_norm_ideal_moebius_le_one
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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open OAI.EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) ≤ M →
        ‖maskedPrincipalRemainder P S W M‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_nonzero_sum_decay (A + 1)
  refine ⟨s, C, hC, ?_⟩
  intro α _ P _ S W M hM hsize
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let N := (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)
  let n := fun E : Finset α => (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hn (E : Finset α) : 0 < n E := by
    dsimp [n]
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))
  have hnN (E : Finset α) (hE : E ∈ S.powerset) : n E ≤ N := by
    have hd := Finset.prod_dvd_prod_of_subset E S P (Finset.mem_powerset.mp hE)
    have hdN := map_dvd Ideal.absNorm hd
    have hpos : 0 < Ideal.absNorm (∏ i ∈ S, P i) := by
      have hh := hn S
      dsimp only [n] at hh
      exact_mod_cast hh
    dsimp only [n, N]
    exact_mod_cast Nat.le_of_dvd hpos hdN
  have ht (E : Finset α) (hE : E ∈ S.powerset) :
      ‖∑' h : O, if h = 0 then 0 else paperRadialFourier W
        (M * ‖eisEmbedding h‖ ^ 2 / n E)‖ ≤ B / (1 + M / n E) ^ (A + 1) := by
    have hscale : 1 ≤ M / n E := (le_div_iff₀ (hn E)).mpr (by simpa using (hnN E hE).trans hsize)
    have h := hb W (M / n E) hscale
    convert h using 1 ; congr 2 ; funext z ; congr 2 ; ring
  let f := fun E : Finset α =>
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
    ∑' h : O, if h = 0 then 0 else paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / n E)
  have hf (E : Finset α) (hE : E ∈ S.powerset) :
      ‖f E‖ ≤ (1 / n E) * (B / (1 + M / n E) ^ (A + 1)) := by
    dsimp [f]
    rw [norm_mul, norm_div, Complex.norm_natCast]
    gcongr
    · exact QuadraticInitialBound.norm_ideal_moebius_le_one _
    · exact ht E hE
  change ‖(M : ℂ) * ∑ E ∈ S.powerset, f E‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  calc
    _ ≤ M * ∑ E ∈ S.powerset, ‖f E‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hM.le
    _ ≤ M * ∑ E ∈ S.powerset, (1 / n E) * (B / (1 + M / n E) ^ (A + 1)) := by
      gcongr with E hE
      exact hf E hE
    _ = ∑ E ∈ S.powerset, (M / n E) * (B / (1 + M / n E) ^ (A + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ ≤ ∑ E ∈ S.powerset, B * (N / M) ^ A := by
      apply Finset.sum_le_sum
      intro E hE
      exact principal_tail_scalar A B (n E) N M hB (hn E) (hnN E hE) hM
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
end OAI.EisensteinSchwartzPoisson
