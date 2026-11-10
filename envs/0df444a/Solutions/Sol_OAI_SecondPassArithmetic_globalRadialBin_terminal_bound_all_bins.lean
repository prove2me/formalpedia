-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalRadialBin_terminal_bound_all_bins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:05:33.620571+00:00
-- url     : https://prove2.me/submissions/f4a05470-41d4-40c5-92f0-cacbf3abef50

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FundamentalDomain
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Theorems.Thm_OAI_SecondPassArithmetic_globalTerminalConstant_nonneg
import Theorems.Thm_OAI_SecondPassArithmetic_globalRadialBin_terminal_bound
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
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
import Theorems.Thm_OAI_SecondPassArithmetic_globalBinRadial_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledLabelScale_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledRowScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooled_J_bound
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
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
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic
open SecondPassIntegration (densityChildEnergy)
namespace OAI.SecondPassArithmetic
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
    (V₁ V₂ : ℝ → ℂ) (C ε θ₁ θ₂ K ell B F A₀ M : ℝ) (N J : ℕ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hK : 0 < K) (hell : 0 < ell) (hB : 1 ≤ B) (hF : 1 ≤ F)
    (hA₀ : 0 ≤ A₀) (hM : 0 ≤ M)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ M) (hV₂ : ∀ t,‖V₂ t‖ ≤ M)
    (hVs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A₀) (hVs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A₀)
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hb₁ : ∀ x∈s,‖ConcreteTraceCRT.eisEmbedding (FirstPassCubeLabels.primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s,‖ConcreteTraceCRT.eisEmbedding (FirstPassCubeLabels.primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    :
    (∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
      globalDescentWeight C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q *
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) V₁ V₂
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J) /
        (globalPooledColumnScale ell j*globalPooledLabelScale j))) ≤
    (C*(1+‖θ₁‖)^(2*J+2)*(1+‖θ₂‖)^(2*J+2)*(globalBinLossScale B j)^ε *
      (globalTerminalConstant A₀ M*globalRayTripleConstant)*K*((ell*B^3)*F)) /
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N := by
  by_cases hs : (globalLogSector p s side j).Nonempty
  · obtain ⟨x,hx⟩ := hs
    obtain ⟨hxs,hj⟩ := Finset.mem_filter.mp hx
    have hJ := globalPooled_J_bound p hp B (zero_lt_one.trans_le hB) side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)
    rw [hj] at hJ
    exact globalRadialBin_terminal_bound p hp hcop hg hc hinj pool Ψ hΨ m V₁ V₂ C ε θ₁ θ₂ K ell B F A₀ M N J
      hC hε hK hell hB hF hA₀ hM hV₁ hV₂ hVs₁ hVs₂ s side j hk hb₁ hb₂ hJ
  · have he : globalBinTriples p s side j=∅ := by
      simp only [globalBinTriples,Finset.not_nonempty_iff_eq_empty.mp hs,Finset.image_empty]
    rw [he]
    simp only [Finset.sum_empty,Finset.sum_const_zero]
    have hB0 := zero_lt_one.trans_le hB
    have hF0 := zero_lt_one.trans_le hF
    have hR := globalBinRadial_pos ell _ hell (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
    have hct := globalTerminalConstant_nonneg A₀ M
    have hl := zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)
    have h4 := globalLogRep_pos j 4
    have hh : 0 ≤ globalBinLossScale B j := by unfold globalBinLossScale;positivity
    unfold globalRayTripleConstant
    positivity
end OAI.SecondPassArithmetic
