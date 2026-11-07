-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.first_ray_energy_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:54:12.278834+00:00
-- url     : https://prove2.me/submissions/aeadfac2-1c5c-4d5e-a64d-297a10e0aac6

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_KernelEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_FirstPassCubeLabels_dilatedCoreRow_integrable
import Theorems.Thm_OAI_FirstPassCubeLabels_firstRayIntegrand_integrable
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_cubeBaseFactor_norm_le_one
import Theorems.Thm_OAI_FirstPassCubeLabels_firstLogDensity_integrable
import Theorems.Thm_OAI_FirstPassCubeLabels_firstLogDensity_nonneg
import Theorems.Thm_OAI_FirstPassCubeLabels_first_cube_energy_small_power
import Theorems.Thm_OAI_FirstPassCubeLabels_rayPairWeight_norm_le
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


attribute [local simp] OAI.FirstPassCubeLabels.coreRayTwist_prod
attribute [local simp] OAI.FirstPassCubeLabels.twisted_core_product

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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportConjugateSum)
open RayFourExpansion (RayCharacter crossCoeff)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (negative : Bool) (r : RayCharacter × RayCharacter) (C : Finset ι → ℂ)
      (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
      (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ)
      (b : Ideal O × O → 𝓢(ℝ, ℂ)) (J : ℕ) (M H Y : ℝ),
      0 ≤ M → 0 ≤ H → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      (∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t) →
      (∑ x ∈ s, ‖w x‖ * ∫ t : ℝ,
        firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r C V y c d
          (ConcretePrimeRowBridge.idealGenerator x.1) x.2 (b x) t) ≤
      (M * H * K * Y ^ deltaLoss * ‖crossCoeff r.1 r.2‖) *
        ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
          ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) C V y c d t z‖ ^ 2 := by
  obtain ⟨K, hK, hpoint⟩ := first_cube_energy_small_power deltaLoss hδ
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc F D B v ε₁ ε₂ hv negative r C V y c d s T w b J M H Y hM hH hY hs hmap hT hnorm hw hdom
  let Ψ := fun t z => dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
    (if negative then r.1 else r.2) C V y c d t z
  let source := fun t : ℝ => ∑ x ∈ s, ‖w x‖ *
    firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r C V y c d
      (ConcretePrimeRowBridge.idealGenerator x.1) x.2 (b x) t
  let target := fun t : ℝ => firstLogDensity J t * ∑ z ∈ T, ‖Ψ t z‖ ^ 2
  have isource : Integrable source volume := by
    apply integrable_finsetSum
    intro x hx
    exact (firstRayIntegrand_integrable p hp hinj hcop hg F D B v ε₁ ε₂ hv negative r C V y c d _ _ (b x)).const_mul ‖w x‖
  have itarget : Integrable target volume := by
    simp only [target, Finset.mul_sum]
    exact integrable_finsetSum _ (fun z hz =>
      dilatedCoreRow_integrable p hp hcop hg F D B v ε₁ ε₂ negative
        (if negative then r.1 else r.2) C V y c d z (firstLogDensity_integrable J))
  have hst (t : ℝ) : source t ≤ (M * H * K * Y ^ deltaLoss * ‖crossCoeff r.1 r.2‖) * target t := by
    let wt := fun x : Ideal O × O => w x * (b x t) *
      cubeBaseFactor p hp hg B v ε₁ ε₂ d x.2 * rayPairWeight p r D x.2
    have hwt (x) (hx : x ∈ s) : ‖wt x‖ ≤ M * H * firstLogDensity J t * ‖crossCoeff r.1 r.2‖ := by
      simp only [wt, norm_mul]
      calc
        _ ≤ M * (H * firstLogDensity J t) * 1 * ‖crossCoeff r.1 r.2‖ := by
          have hden := firstLogDensity_nonneg J t
          gcongr <;> first
            | positivity
            | exact hw x hx
            | exact hdom x hx t
            | exact cubeBaseFactor_norm_le_one p hp hcop hg hc B v ε₁ ε₂ d x.2
            | exact rayPairWeight_norm_le p hinj hc r D x.2
        _ = _ := by ring
    have hh := hpoint p hp hinj hcop hg F D B v ε₁ ε₂ hv negative
      (if negative then r.1 else r.2) C V y t c d s T wt
      (M * H * firstLogDensity J t * ‖crossCoeff r.1 r.2‖) Y
      (by exact mul_nonneg (mul_nonneg (mul_nonneg hM hH) (firstLogDensity_nonneg J t)) (norm_nonneg _))
      hY hs hmap hT hnorm hwt
    convert hh using 1
    · apply Finset.sum_congr rfl
      intro x hx
      simp only [firstRayIntegrand, wt, norm_mul]
      ring
    · dsimp only [target, Ψ, dilatedCoreRow]
      ring
  calc
    _ = ∫ t : ℝ, source t := by
      rw [integral_finsetSum _ (fun x hx =>
        (firstRayIntegrand_integrable p hp hinj hcop hg F D B v ε₁ ε₂ hv negative r C V y c d _ _ (b x)).const_mul ‖w x‖)]
      exact Finset.sum_congr rfl (fun x hx => (integral_const_mul _ _).symm)
    _ ≤ ∫ t : ℝ, (M * H * K * Y ^ deltaLoss * ‖crossCoeff r.1 r.2‖) * target t :=
      integral_mono isource (itarget.const_mul _) hst
    _ = _ := integral_const_mul _ _
end OAI.FirstPassCubeLabels
