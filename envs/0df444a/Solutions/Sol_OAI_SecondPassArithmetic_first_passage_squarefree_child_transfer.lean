-- Prove2me | solution 1 for OAI.SecondPassArithmetic.first_passage_squarefree_child_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:22:50.263826+00:00
-- url     : https://prove2.me/submissions/8c128041-0aef-42c9-8f61-b212397dc85d

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicSectors
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SquarefreeTransfer
import Theorems.Thm_OAI_SecondPassArithmetic_firstInputFamilyEnergy_squarefree_transfer
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_ne_zero
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_firstLogDensity_nonneg
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_first_passage_transfer_input_family
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.spatialTriple_one
attribute [local simp] OAI.CubicEisenstein.spatialTriple_two
attribute [local simp] OAI.CubicEisenstein.spatialTriple_zero
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
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply



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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel firstLogDensity
  actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F B C D : Finset ι) (hFB : Disjoint F B) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O)
    (hΨ₁ : ∀ a, ‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a, ‖Ψ₂ a‖ ≤ 1)
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ))
    (U₁ U₂ : ℝ → ℂ) (hUc₁ : HasCompactSupport U₁) (hUs₁ : ContDiff ℝ ∞ U₁)
    (hUc₂ : HasCompactSupport U₂) (hUs₂ : ContDiff ℝ ∞ U₂)
    (hU₁ : ∀ t, g₁ t ≠ 0 → U₁ t=1) (hU₂ : ∀ t, g₂ t ≠ 0 → U₂ t=1)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ N₁ N₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ M₁) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ M₂)
    (hV₁ : ∀ t, V₁ t ≠ 0 → |t| ≤ N₁) (hV₂ : ∀ t, V₂ t ≠ 0 → |t| ≤ N₂)
    (ε deltaLoss : ℝ) (hε : 0 < ε) (hδ : 0 < deltaLoss) (tailOrder decayOrder J : ℕ) :
    ∃ (data₁ data₂ : SquarefreeBudgetData) (K₀ : ℝ), 0 ≤ K₀ ∧
      ∀ (lengthScale : ℝ), 0 < lengthScale → ∀ (s : Finset (Ideal O × O)) (T : Finset O)
        (w : Ideal O × O → ℂ) (M Y Z : ℝ),
      0 ≤ M → 0 < Y → 0 ≤ Z →
      (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
      let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B (fun i => v₁ i+v₂ i) ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true
          (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S)))
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false
          (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S)))
          c (ConcretePrimeRowBridge.idealGenerator x.1)) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale/‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖) *
        (M*K₀*Y^deltaLoss) *
        Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z) *
        Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z) := by
  obtain ⟨windows₁,A₁,S₁,H₁,Q₁,hA₁,hS₁,hH₁,hQ₁,hleft⟩ :=
    firstInputFamilyEnergy_squarefree_transfer p hp hcop hg hinj hc hpr U₁ hUc₁ hUs₁
      g₁ V₁ true hU₁ M₁ hM₁ hg₁ ε hε tailOrder decayOrder J
  obtain ⟨windows₂,A₂,S₂,H₂,Q₂,hA₂,hS₂,hH₂,hQ₂,hright⟩ :=
    firstInputFamilyEnergy_squarefree_transfer p hp hcop hg hinj hc hpr U₂ hUc₂ hUs₂
      g₂ V₂ false hU₂ M₂ hM₂ hg₂ ε hε tailOrder decayOrder J
  let data₁ : SquarefreeBudgetData := ⟨windows₁,A₁,S₁,H₁,Q₁,hA₁,hS₁,hH₁,hQ₁⟩
  let data₂ : SquarefreeBudgetData := ⟨windows₂,A₂,S₂,H₂,Q₂,hA₂,hS₂,hH₂,hQ₂⟩
  obtain ⟨K₀,hK₀,hfirst⟩ := first_passage_transfer_input_family p hp hinj hcop hg hc hpr
    F B hFB (fun i => v₁ i+v₂ i) ε₁ ε₂ hv Ψ₁ Ψ₂ m₁ m₂
    (fun S => g₁ (columnLog p X₁ S)) (fun S => g₂ (columnLog p X₂ S))
    (fun G hG => hΨ₁ _) (fun G hG => hΨ₂ _) W V₁ V₂ X₁ X₂ hX₁ hX₂
    N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  let I₀ : ℝ := ∫ t, firstLogDensity 0 t
  have hI₀ : 0 ≤ I₀ := integral_nonneg (FirstPassCubeLabels.firstLogDensity_nonneg 0)
  refine ⟨data₁,data₂,K₀*I₀,mul_nonneg hK₀ hI₀,?_⟩
  intro lengthScale hL s T w M Y Z hM hY hZ hs hs0 hmap hT0 hT hw
  dsimp only
  have h₁ := hleft Y hY B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z T hv hCB hD hΨ₁ hX₁ hZ hT hT0
  have h₂ := hright Y hY B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z T hv hCB hD hΨ₂ hX₂ hZ hT hT0
  change _ ≤ I₀*firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
    tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z at h₁
  change _ ≤ I₀*firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
    tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z at h₂
  have hb := hfirst lengthScale hL (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) (primeSubsetGenerator_ne_zero _ _)
    s T w M Y hM hY.le hs hs0 hmap hT0 hT hw
  apply hb.trans
  calc
    _ ≤ (lengthScale/‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖) *
        (M*K₀*Y^deltaLoss) *
        Real.sqrt (I₀*firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z) *
        Real.sqrt (I₀*firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul hI₀, Real.sqrt_mul hI₀]
      calc
        _ = (lengthScale/‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖) *
          (M*K₀*Y^deltaLoss) * (Real.sqrt I₀)^2 *
          Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
            tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z) *
          Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
            tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z) := by ring
        _ = _ := by rw [Real.sq_sqrt hI₀]; ring
end OAI.SecondPassArithmetic
