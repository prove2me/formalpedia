-- Prove2me | solution 1 for OAI.QuadraticMainBoundary.main_boundary_localization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:10:39.607447+00:00
-- url     : https://prove2.me/submissions/cfa2f3e6-7258-491b-ad68-23fbded920c1

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeLabels
import Theorems.Thm_OAI_QuadraticSquarefreeKernel_norm_decomposition
import Theorems.Thm_OAI_QuadraticMainBoundary_norm_pos
import Theorems.Thm_OAI_QuadraticMainBoundary_norm_one_le
import Theorems.Thm_OAI_QuadraticMainBoundary_norm_le_of_dvd
import Theorems.Thm_OAI_QuadraticMainBoundary_cutoffDifference_nonzero_iff
import Theorems.Thm_OAI_QuadraticMainBoundary_squarePart_dvd
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
open OAI.QuadraticMainBoundary
open scoped BigOperators Classical
open UniqueFactorizationMonoid
open QuadraticSquarefreeKernel
namespace OAI.QuadraticMainBoundary
theorem _root_.solution (K : ℝ) {G H D E : Ideal O}
    (hG : G ≠ 0) (hH : Squarefree H) (hDG : D ∣ G) (hEG : E ∣ G)
    (h : cutoffDifference K H D ≠ 0) :
    K < (Ideal.absNorm (H * D * E) : ℝ) ∧
    (Ideal.absNorm (H * D * E) : ℝ) ≤ K * (Ideal.absNorm G : ℝ) ^ 2 ∧
    squarePart (H * D * E) ∣ G ∧
    K / (Ideal.absNorm G : ℝ) ^ 2 < (Ideal.absNorm (squarefreePart (H * D * E)) : ℝ) ∧
    (Ideal.absNorm (squarefreePart (H * D * E)) : ℝ) ≤ K * (Ideal.absNorm G : ℝ) ^ 2 := by
  have hD := ne_zero_of_dvd_ne_zero hG hDG
  have hE := ne_zero_of_dvd_ne_zero hG hEG
  have hB0 : H * D * E ≠ 0 := mul_ne_zero (mul_ne_zero hH.ne_zero hD) hE
  obtain ⟨hHK, hKHD⟩ := (cutoffDifference_nonzero_iff K H D hD).mp h
  have hHpos := norm_pos hH.ne_zero
  have hDpos := norm_pos hD
  have hEpos := norm_pos hE
  have hGone := norm_one_le hG
  have hEone := norm_one_le hE
  have hDle := norm_le_of_dvd hG hDG
  have hEle := norm_le_of_dvd hG hEG
  have hK : 0 ≤ K := le_trans hHpos.le hHK
  have hBlo : K < (Ideal.absNorm (H * D * E) : ℝ) := by
    rw [map_mul, Nat.cast_mul]
    have hp := Nat.cast_nonneg (Ideal.absNorm (H * D)) (α := ℝ)
    nlinarith
  have hBhi : (Ideal.absNorm (H * D * E) : ℝ) ≤ K * (Ideal.absNorm G : ℝ) ^ 2 := by
    simp only [map_mul, Nat.cast_mul]
    calc
      (Ideal.absNorm H : ℝ) * Ideal.absNorm D * Ideal.absNorm E ≤
        K * Ideal.absNorm G * Ideal.absNorm G :=
        mul_le_mul (mul_le_mul hHK hDle hDpos.le hK) hEle hEpos.le (by positivity)
      _ = _ := by ring
  have hroot := squarePart_dvd hG hH hDG hEG
  have hrootle := norm_le_of_dvd hG hroot
  have hrootone := norm_one_le (squarePart_ne_zero hB0)
  have hkerpos := norm_pos (squarefree_squarefreePart (H * D * E)).ne_zero
  have hdecomp : (Ideal.absNorm (squarePart (H * D * E)) : ℝ) ^ 2 *
      Ideal.absNorm (squarefreePart (H * D * E)) = Ideal.absNorm (H * D * E) := by
    exact_mod_cast norm_decomposition (H * D * E)
  have hrootpow : (Ideal.absNorm (squarePart (H * D * E)) : ℝ) ^ 2 ≤
      (Ideal.absNorm G : ℝ) ^ 2 := pow_le_pow_left₀ (le_trans zero_le_one hrootone) hrootle 2
  refine ⟨hBlo, hBhi, hroot, ?_, ?_⟩
  · apply (div_lt_iff₀ (by positivity : 0 < (Ideal.absNorm G : ℝ) ^ 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hrootpow hkerpos.le]
  · have hrpow : 1 ≤ (Ideal.absNorm (squarePart (H * D * E)) : ℝ) ^ 2 := by nlinarith
    nlinarith
end OAI.QuadraticMainBoundary
