-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.first_passage_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:20:52.692678+00:00
-- url     : https://prove2.me/submissions/455f33fb-8a07-4945-8bc2-8f8cfcf5e8e5

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FirstPassage
import Theorems.Thm_OAI_FirstPassCubeLabels_first_column_energy_integral
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_actual_first_kernel_uniform_energy_envelope
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_firstColumnEnergy_nonneg
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
open OAI.FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)
open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (C₁ C₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale → ∀ c d : O, d ≠ 0 →
      ∀ (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true C₁ c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false C₂ c (ConcretePrimeRowBridge.idealGenerator x.1))
        W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ c d J T) *
        Real.sqrt (firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ c d J T) := by
  obtain ⟨H, hH, hsep⟩ := actual_first_kernel_uniform_energy_envelope p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ 0 J
  obtain ⟨K, hK, hpush⟩ := first_column_energy_integral deltaLoss hδ
  refine ⟨H * K, mul_nonneg hH hK.le, ?_⟩
  intro lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  let A₁ := fun x : Ideal O × O => originalLabelColumn p hg B ε₁ ε₂ true C₁ c (ConcretePrimeRowBridge.idealGenerator x.1)
  let A₂ := fun x : Ideal O × O => originalLabelColumn p hg B ε₁ ε₂ false C₂ c (ConcretePrimeRowBridge.idealGenerator x.1)
  let q := lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖
  have hq : 0 ≤ q := div_nonneg hL.le (norm_nonneg _)
  have hfam : ∀ x : Ideal O × O, ∃ b : 𝓢(ℝ, ℂ), x ∈ s →
      (∀ t : ℝ, ‖b t‖ ≤ H * firstLogDensity J t) ∧
      ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ (A₁ x) (A₂ x) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
        q * Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true (A₁ x) V₁ X₁ d x.2 b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false (A₂ x) V₂ X₂ d x.2 b) := by
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨b, hb, hk⟩ := hsep lengthScale hL d x.2 hd (hnonzero x hx)
      refine ⟨b, fun _ => ⟨?_, hk (A₁ x) (A₂ x)⟩⟩
      simpa only [pow_zero, one_mul] using hb
    · exact ⟨0, fun hx' => (hx hx').elim⟩
  choose b hb using hfam
  let E₁ := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true (A₁ x) V₁ X₁ d x.2 (b x)
  let E₂ := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false (A₂ x) V₂ X₂ d x.2 (b x)
  let O₁ := firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ c d J T
  let O₂ := firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ c d J T
  let P := M * H * K * Y ^ deltaLoss
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg (mul_nonneg hM hH) hK.le) (Real.rpow_nonneg hY deltaLoss)
  have hE₁ (x) : 0 ≤ E₁ x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ true _ _ _ _ _ _
  have hE₂ (x) : 0 ≤ E₂ x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ false _ _ _ _ _ _
  have hdom : ∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t := fun x hx => (hb x hx).1
  have hsum₁ : (∑ x ∈ s, ‖w x‖ * E₁ x) ≤ P * O₁ :=
    hpush p hp hinj hcop hg hc F B v ε₁ ε₂ hv true C₁ V₁ X₁ c d s T w b J M H Y
      hM hH hY hs hmap hT hnorm hw hdom
  have hsum₂ : (∑ x ∈ s, ‖w x‖ * E₂ x) ≤ P * O₂ :=
    hpush p hp hinj hcop hg hc F B v ε₁ ε₂ hv false C₂ V₂ X₂ c d s T w b J M H Y
      hM hH hY hs hmap hT hnorm hw hdom
  have hterm (x) : ‖w x‖ * (Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) =
      Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x) := by
    rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_mul (norm_nonneg _)]
    calc
      _ = (Real.sqrt ‖w x‖) ^ 2 * (Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) := by
        rw [Real.sq_sqrt (norm_nonneg _)]
      _ = _ := by ring
  calc
    _ ≤ ∑ x ∈ s, ‖w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (A₁ x) (A₂ x) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ s, q * (Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x)) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, ← hterm]
      calc
        _ ≤ ‖w x‖ * (q * Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) :=
          mul_le_mul_of_nonneg_left (hb x hx).2 (norm_nonneg _)
        _ = _ := by ring
    _ = q * (∑ x ∈ s, Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ q * (Real.sqrt (∑ x ∈ s, ‖w x‖ * E₁ x) * Real.sqrt (∑ x ∈ s, ‖w x‖ * E₂ x)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le s
        (fun x => mul_nonneg (norm_nonneg _) (hE₁ x))
        (fun x => mul_nonneg (norm_nonneg _) (hE₂ x))) hq
    _ ≤ q * (Real.sqrt (P * O₁) * Real.sqrt (P * O₂)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt hsum₁) (Real.sqrt_le_sqrt hsum₂)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hq
    _ = _ := by
      rw [Real.sqrt_mul hP, Real.sqrt_mul hP]
      calc
        _ = q * (Real.sqrt P)^2 * Real.sqrt O₁ * Real.sqrt O₂ := by ring
        _ = _ := by rw [Real.sq_sqrt hP]; dsimp only [P]; ring
end OAI.FirstPassCubeLabels
