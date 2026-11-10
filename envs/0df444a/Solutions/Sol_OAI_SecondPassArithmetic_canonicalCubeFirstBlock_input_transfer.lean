-- Prove2me | solution 1 for OAI.SecondPassArithmetic.canonicalCubeFirstBlock_input_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:02:14.672191+00:00
-- url     : https://prove2.me/submissions/87fa194d-7fd0-4785-b611-473dffd71ceb

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_QuantitativePassage
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_ne_zero
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
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
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_CubeCoordinates_support_pos
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_firstInputFamilyEnergy_nonneg
import Theorems.Thm_OAI_SecondPassArithmetic_first_passage_full_uniform_input_family
import Theorems.Thm_OAI_SecondPassArithmetic_globalBinFirstCoefficient_nonneg
import Theorems.Thm_OAI_SecondPassArithmetic_globalCubeCoefficient_side
import Theorems.Thm_OAI_SecondPassArithmetic_globalCubeColumnScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalCube_first_scalar_bound
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledRowScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_apply
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_source
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.kernelLocalLift_symm
attribute [local simp] OAI.CubicEisenstein.kernelQuotientChart_symm
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
attribute [local simp] OAI.InitialMeanSquare.initialLogProfile_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.append_first
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.first_append
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.source_append
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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (W V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ : ℝ) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤M₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    ∃ C : ℝ,0≤C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ : 𝓢(ℝ,ℂ)) (K ell B F Ymax : ℝ),
      0<K → 0<ell → 0<B → 0<F →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,canonicalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      C*Ymax^deltaLoss*
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F true b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)) *
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F false b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)) := by
  obtain ⟨C,hC,hfirst⟩ := first_passage_full_uniform_input_family W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F Ymax hK hell hB hF hΨ₁ hΨ₂ hw ha hYmax hsf hs0 hmap hT0 hT
  by_cases hempty : blocks=∅
  · subst blocks
    simp only [Finset.sum_empty,mul_zero,norm_zero,Real.sqrt_zero,le_refl]
  have hne : blocks.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let E₁ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)
  let E₂ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)
  let v := fun b => w b*globalCubeCoefficient p K ell B F true b
  have hv (b) (hb : b∈blocks) : 0≤v b := mul_nonneg (hw b hb)
    (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hE₁ (b) : 0≤E₁ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hE₂ (b) : 0≤E₂ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hden : 0<ell*B^2*F := by positivity
  have hYmax0 : 0≤Ymax := by
    obtain ⟨b,hb⟩ := hne
    exact (globalPooledRowScale_pos K ell B F hK hell hB hF _).le.trans (hYmax b hb)
  have hpref : 0≤C*Ymax^deltaLoss := mul_nonneg hC (Real.rpow_nonneg hYmax0 deltaLoss)
  have hpoint (b) (hb : b∈blocks) : (ell*B^2*F)⁻¹*
      ‖canonicalCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      (C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
    have hFB : Disjoint (globalCubePool pool b) b.cube.support := by
      apply Finset.disjoint_left.mpr
      intro i hi hiB
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB)
    have hX₁ := globalCubeColumnScale_pos p hp ell hell true b
    have hX₂ := globalCubeColumnScale_pos p hp ell hell false b
    have hD := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor
    have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalFirstIndex p true (b.withCommon ∅))
    have hh := hfirst p hp hinj hcop hg hc hpr (globalCubePool pool b) b.cube.support hFB
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit b.cube.support_pos
      Ψ₁ Ψ₂ m₁ m₂ (fun A => g₁ (columnLog p (globalCubeColumnScale p ell true b) A))
      (fun A => g₂ (columnLog p (globalCubeColumnScale p ell false b) A))
      (fun A hA => hΨ₁ _) (fun A hA => hΨ₂ _)
      _ _ hX₁ hX₂ K hK (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) (primeSubsetGenerator_ne_zero _ _)
      (s b) (T b) (a b) (w b) (globalFirstPooledRow p K ell B F true (b.withCommon ∅))
      (hw b hb) hY.le (hsf b hb) (hs0 b hb) (hmap b hb) (hT0 b hb) (hT b hb) (ha b hb)
    have hscl := globalCube_first_scalar_bound p hp K ell B F hK hell hB hF b
    have hpow := Real.rpow_le_rpow hY.le (hYmax b hb) hδ.le
    have hmul := mul_le_mul_of_nonneg_left hh
      (show 0≤(ell*B^2*F)⁻¹*(primeProductNorm p b.firstDivisor)⁻¹ by positivity)
    simp only [canonicalCubeFirstBlock,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_of_nonneg hD.le,←mul_assoc]
    apply hmul.trans
    calc
      _ = ((ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
          ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
            (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))*
          (w b*C*(globalFirstPooledRow p K ell B F true (b.withCommon ∅))^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by dsimp [E₁,E₂,globalCubeInputFamilyEnergy];ring
      _ ≤ globalCubeCoefficient p K ell B F true b*(w b*C*Ymax^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        apply mul_le_mul hscl
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hw b hb) hC))
          (mul_nonneg (mul_nonneg (hw b hb) hC) (Real.rpow_nonneg hY.le _))
          (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
      _ = _ := by dsimp [v];ring
  rw [norm_mul, norm_inv]
  have hn : ‖(ell*B^2*F : ℂ)‖=ell*B^2*F := by
    norm_cast
    exact abs_of_pos hden
  rw [hn]
  calc
    _ ≤ (ell*B^2*F)⁻¹*∑ b∈blocks,‖canonicalCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hden.le)
    _ ≤ ∑ b∈blocks,(C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ = (C*Ymax^deltaLoss)*∑ b∈blocks,Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Real.sqrt_mul (hv b hb),Real.sqrt_mul (hv b hb)]
      have hs := Real.sq_sqrt (hv b hb)
      calc
        _ = (C*Ymax^deltaLoss)*(Real.sqrt (v b))^2*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by rw [hs]
        _ = _ := by ring
    _ ≤ (C*Ymax^deltaLoss)*(Real.sqrt (∑ b∈blocks,v b*E₁ b)*Real.sqrt (∑ b∈blocks,v b*E₂ b)) :=
      mul_le_mul_of_nonneg_left (by
        have hcauchy := Real.sum_sqrt_mul_sqrt_le blocks.attach
          (fun b => mul_nonneg (hv b.val b.property) (hE₁ b.val))
          (fun b => mul_nonneg (hv b.val b.property) (hE₂ b.val))
        simpa only [Finset.sum_attach (f := fun b => Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b)),
          Finset.sum_attach (f := fun b => v b*E₁ b),Finset.sum_attach (f := fun b => v b*E₂ b)] using hcauchy) hpref
    _ = _ := by simp only [v,E₁,E₂,globalCubeCoefficient_side,mul_assoc]
end OAI.SecondPassArithmetic
