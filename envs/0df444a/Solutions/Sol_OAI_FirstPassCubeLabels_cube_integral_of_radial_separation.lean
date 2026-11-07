-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.cube_integral_of_radial_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:07:01.909859+00:00
-- url     : https://prove2.me/submissions/ea105f00-6c11-48af-8806-da676897e140

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayExpansion
import Theorems.Thm_OAI_FirstPassCubeLabels_sum_threeGaussRowFactor_eq_ideal_rows
import Theorems.Thm_OAI_FirstPassCubeLabels_threeGaussRowFactor_log_twist
import Theorems.Thm_OAI_FirstPassCubeLabels_integrable_log_pair
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
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (y₁ y₂ : Finset ι → ℝ) (R : ℝ)
    (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ x y : ℝ, V₁ x * V₂ y * paperRadialFourier W (R * Real.exp (-x-y)) =
      ∫ t : ℝ, (V₁ x * FourierBridge.logPhase t (-x)) *
        (V₂ y * FourierBridge.logPhase t (-y)) * b t) :
    Integrable (fun t : ℝ => b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h) volume ∧
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      (V₁ (y₁ N) * V₂ (y₂ P) * paperRadialFourier W (R * Real.exp (-(y₁ N)-y₂ P))) *
        threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
    ∫ t : ℝ, b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h := by
  let G : ℝ → Finset ι → Finset ι → ℂ := fun t N P => if Disjoint N P then
    b t * threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h else 0
  have hGint (N P : Finset ι) : Integrable (fun t => G t N P) volume := by
    by_cases hd : Disjoint N P
    · simp only [G, if_pos hd]
      convert integrable_log_pair b (-(y₁ N)) (-(y₂ P))
        (V₁ (y₁ N) * V₂ (y₂ P) * threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h) using 1
      funext t
      rw [threeGaussRowFactor_log_twist]
      ring
    · simp only [G, if_neg hd]
      exact integrable_zero _ _ _
  have hGsum (t : ℝ) :
      (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P) =
        b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        idealPairReindex p hg F
          (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
          (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h := by
    calc
      _ = b t * (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
          (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h else 0) := by
            simp only [G, Finset.mul_sum, mul_ite, mul_zero]
      _ = _ := by
        rw [sum_threeGaussRowFactor_eq_ideal_rows p hp hinj hcop hg hc hpr F B hFB]
        ring
  have hint : Integrable (fun t => ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P) volume :=
    integrable_finsetSum _ (fun N _ => integrable_finsetSum _ (fun P _ => hGint N P))
  constructor
  · simpa only [hGsum] using hint
  · have hterm (N P : Finset ι) :
        (if Disjoint N P then
          (V₁ (y₁ N) * V₂ (y₂ P) * paperRadialFourier W (R * Real.exp (-(y₁ N)-y₂ P))) *
            threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
        ∫ t : ℝ, G t N P := by
      by_cases hd : Disjoint N P
      · simp only [G, if_pos hd]
        rw [hsep (y₁ N) (y₂ P), ← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with t
        rw [threeGaussRowFactor_log_twist]
        ring
      · simp [G, hd]
    calc
      _ = ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, ∫ t : ℝ, G t N P := by
        apply Finset.sum_congr rfl
        intro N hN
        exact Finset.sum_congr rfl (fun P hP => hterm N P)
      _ = ∫ t : ℝ, ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P := by
        rw [integral_finsetSum _ (fun N _ => integrable_finsetSum _ (fun P _ => hGint N P))]
        apply Finset.sum_congr rfl
        intro N hN
        exact (integral_finsetSum _ (fun P _ => hGint N P)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hGsum t
end OAI.FirstPassCubeLabels
