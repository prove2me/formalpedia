-- Prove2me | solution 1 for OAI.SecondPassArithmetic.actualSecondKernel_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:23:44.709257+00:00
-- url     : https://prove2.me/submissions/412e308a-5ea3-40f3-a85d-77709f8d288f

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayCoefficients
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SecondPoisson
import Theorems.Thm_OAI_SecondPassArithmetic_secondGaussTerm_log_twist
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_actual_radial_argument
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_integrable_log_pair
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



set_option autoImplicit false
open OAI
noncomputable section
open OAI.SecondPassArithmetic
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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open FirstPassCubeLabels (columnLog primeProductNorm firstDualScale normalizedColumn)
open FourierBridge (logPhase)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ x y : ℝ, star (V₁ x) * V₂ y *
      paperRadialFourier W (firstDualScale p ∅ Y X₁ X₂ e k * Real.exp (-x-y)) =
      ∫ t : ℝ, (star (V₁ x) * logPhase t (-x)) * (V₂ y * logPhase t (-y)) * b t) :
    Integrable (fun t : ℝ => b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
      (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false)) volume ∧
    actualSecondKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y =
      (Y : ℂ) * ∫ t : ℝ, b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
        (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) := by
  let G := fun (t : ℝ) (S T : Finset ι) => if Disjoint S T then b t *
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
      (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) S T else 0
  have hGi (S T : Finset ι) : Integrable (fun t => G t S T) volume := by
    by_cases hd : Disjoint S T
    · simp only [G, if_pos hd, secondGaussTerm_log_twist]
      convert FirstPassCubeLabels.integrable_log_pair b (-(columnLog p X₁ S)) (-(columnLog p X₂ T))
        (star (V₁ (columnLog p X₁ S)) * V₂ (columnLog p X₂ T) *
          secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
            (normalizedColumn p (fun _ => 1)) (normalizedColumn p (fun _ => 1)) S T) using 1
    · simp only [G, if_neg hd]
      exact integrable_zero _ _ _
  have hGs (t : ℝ) : (∑ S ∈ F.powerset, ∑ T ∈ F.powerset, G t S T) =
      b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
        (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) := by
    simp only [G, secondActualPair, secondGaussTerm, Finset.mul_sum, mul_ite, mul_zero]
  have hI : Integrable (fun t => ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, G t S T) volume :=
    integrable_finsetSum _ (fun S _ => integrable_finsetSum _ (fun T _ => hGi S T))
  constructor
  · simpa only [hGs] using hI
  · rw [← integral_congr_ae (Filter.Eventually.of_forall hGs)]
    rw [integral_finsetSum _ (fun S _ => integrable_finsetSum _ (fun T _ => hGi S T)), Finset.mul_sum]
    unfold actualSecondKernel
    apply Finset.sum_congr rfl
    intro S hS
    rw [integral_finsetSum _ (fun T _ => hGi S T), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    by_cases hd : Disjoint S T
    · simp only [G, if_pos hd, secondGaussTerm_log_twist]
      have harg := FirstPassCubeLabels.actual_radial_argument p hp S T ∅ hd
        (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) Y X₁ X₂ hX₁ hX₂ e k
      simp only [Finset.union_empty] at harg
      rw [← harg]
      have hn : secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
          (normalizedColumn p (fun _ => 1)) (normalizedColumn p (fun _ => 1)) S T =
        ((‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)⁻¹ * (‖eisEmbedding (∏ i ∈ T, p i)‖ : ℂ)⁻¹) *
          secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T := by
        simp only [secondGaussTerm, secondInputCoefficient, normalizedColumn, one_div,
          mul_one, star_mul, map_inv₀, Complex.star_def, Complex.conj_ofReal]
        ring
      rw [hn]
      rw [Finset.prod_union hd]
      simp only [map_mul, norm_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
      have hh := congrArg (fun z : ℂ => (Y : ℂ) * z *
        ((‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)⁻¹ * (‖eisEmbedding (∏ i ∈ T, p i)‖ : ℂ)⁻¹) *
          secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T)
        (hsep (columnLog p X₁ S) (columnLog p X₂ T))
      rw [← integral_const_mul, ← integral_mul_const, ← integral_mul_const] at hh
      convert hh using 1
      · ring
      · rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        ring
    · simp [hd, G]
end OAI.SecondPassArithmetic
