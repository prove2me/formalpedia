-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.actual_first_kernel_to_ideal_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:10:43.145429+00:00
-- url     : https://prove2.me/submissions/2575a9c4-a5e4-414c-93bb-9f99bcead25a

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayExpansion
import Theorems.Thm_OAI_FirstPassCubeLabels_two_variable_radial_separation
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
import Theorems.Thm_OAI_FirstPassCubeLabels_actual_radial_argument
import Theorems.Thm_OAI_FirstPassCubeLabels_actual_pair_prefactor
import Theorems.Thm_OAI_FirstPassCubeLabels_cube_integral_of_radial_separation
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
open scoped BigOperators Classical
open OAI.FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ K ∧
        Integrable (fun t : ℝ => b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
          idealPairReindex p hg F
            (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂
              (logTwistMinus (normalizedColumn p C₁) V₁ (columnLog p X₁) t) d)
            (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂
              (logTwistPlus (normalizedColumn p C₂) V₂ (columnLog p X₂) t) d) h) volume ∧
        (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
          (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P)) *
          ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
          paperRadialFourier W (lengthScale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂))) *
          threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
        ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
        ∫ t : ℝ, b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
          idealPairReindex p hg F
            (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂
              (logTwistMinus (normalizedColumn p C₁) V₁ (columnLog p X₁) t) d)
            (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂
              (logTwistPlus (normalizedColumn p C₂) V₂ (columnLog p X₂) t) d) h := by
  obtain ⟨K, hK, hs⟩ := two_variable_radial_separation W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL d h hd hh
  let R := firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h
  have hR : 0 < R := by
    unfold R firstDualScale
    exact div_pos (mul_pos hL (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hb, hi, hbound⟩ := hs R hR
  have hpair := cube_integral_of_radial_separation p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂
    (normalizedColumn p C₁) (normalizedColumn p C₂) d h W V₁ V₂ (columnLog p X₁) (columnLog p X₂) R b hb
  refine ⟨b, hi, hbound, hpair.1, ?_⟩
  rw [← hpair.2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · rw [if_pos hNP, if_pos hNP]
    have hNB : Disjoint N B := hFB.mono_left (Finset.mem_powerset.mp hN)
    have hPB : Disjoint P B := hFB.mono_left (Finset.mem_powerset.mp hP)
    have harg := actual_radial_argument p hp N P (cubeActiveSupport B v ε₁ ε₂) hNP
      (hNB.mono_right (Finset.filter_subset _ _)) (hPB.mono_right (Finset.filter_subset _ _))
      lengthScale X₁ X₂ hX₁ hX₂ d h
    change R * Real.exp (-(columnLog p X₁ N) - columnLog p X₂ P) = _ at harg
    rw [harg]
    have hpre := actual_pair_prefactor p hp hcop hg N P B hNP hNB hPB v ε₁ ε₂ C₁ C₂ lengthScale d h
    calc
      _ = (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P) *
          paperRadialFourier W (lengthScale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)))) *
          (((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
            threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h) := by ring
      _ = _ := by rw [hpre]; ring
  · simp [hNP]
end OAI.FirstPassCubeLabels
