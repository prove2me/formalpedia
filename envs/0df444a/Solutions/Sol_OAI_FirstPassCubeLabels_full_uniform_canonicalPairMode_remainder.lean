-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.full_uniform_canonicalPairMode_remainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:02:09.798348+00:00
-- url     : https://prove2.me/submissions/3ea68b4e-06fb-428f-abf7-914b38ce0a26

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HighRadialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PaddedPassage
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceRemainders
import Theorems.Thm_OAI_FirstPassCubeLabels_canonicalPairMode_norm_le
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
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_lattice_summable_norm
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_lattice_tail
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
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
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
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply



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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnPrimeCoprime)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
      (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
      (X₁ X₂ K H : ℝ),0<K → 0≤H → ∀(d : O),d≠0 → ∀T:Finset O,
      let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
      let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
      (∀h:O,h∉T → H≤scale*‖eisEmbedding h‖^2) →
      ‖∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖))*
      ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hcop hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K H hK hH d hd T
  dsimp only
  intro hT
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
  let c := ‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖)
  have hscale : 0<scale := div_pos hK (mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))) (primeProductNorm_pos p hp S))
  have hc0 : 0≤c := by dsimp [c]; positivity
  let small : Set O := {h|h∉T}
  let large : Set O := {h|H≤scale*‖eisEmbedding h‖^2}
  let f : small→large := fun h=>⟨h.val,hT h.val h.property⟩
  have hfi : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x:large=>x.val) hab)
  have hrad := EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hscale
  have hmajor := (hrad.subtype small).mul_left c
  have hpnt (h:small) :
      ‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      c*‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
    canonicalPairMode_norm_le p hp hcop hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d h.val
  have hsmall := Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑'h:small,‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖ :=
      norm_tsum_le_tsum_norm hsmall
    _ ≤ ∑'h:small,c*‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
      hsmall.tsum_le_tsum hpnt hmajor
    _ = c*∑'h:small,‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ := tsum_mul_left
    _ ≤ c*∑'h:large,‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
      mul_le_mul_of_nonneg_left ((hrad.subtype small).tsum_le_tsum_of_inj f hfi
        (fun _ _=>norm_nonneg _) (fun _=>le_rfl) (hrad.subtype large)) hc0
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb W scale H hscale hH) hc0
end OAI.FirstPassCubeLabels
