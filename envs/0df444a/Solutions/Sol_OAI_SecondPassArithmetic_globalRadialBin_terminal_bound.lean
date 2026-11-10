-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalRadialBin_terminal_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:01:37.913199+00:00
-- url     : https://prove2.me/submissions/43a9a812-ea72-4a02-8917-eff6fc6a8d57

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FundamentalDomain
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Theorems.Thm_OAI_SecondPassIntegration_childDensity_elementary_all_scales
import Theorems.Thm_OAI_SecondPassArithmetic_globalTerminalConstant_nonneg
import Theorems.Thm_OAI_SecondPassArithmetic_radial_decay_step
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledRow_radial_bound
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
import Theorems.Thm_OAI_SecondPassArithmetic_globalArithmeticTargets_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_globalBinRadial_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalDescentWeight_mass
import Theorems.Thm_OAI_SecondPassArithmetic_globalDescentWeight_nonneg
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledColumnScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledLabelScale_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledRowScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_secondRayMinus_norm_le
import Theorems.Thm_OAI_SecondPassArithmetic_secondRayPlus_norm_le
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
    (hJ : globalLogRep j 4 ≤ B^2) :
    (∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
      globalDescentWeight C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q *
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) V₁ V₂
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J) /
        (globalPooledColumnScale ell j*globalPooledLabelScale j))) ≤
    (C*(1+‖θ₁‖)^(2*J+2)*(1+‖θ₂‖)^(2*J+2)*(globalBinLossScale B j)^ε *
      (globalTerminalConstant A₀ M*globalRayTripleConstant)*K*((ell*B^3)*F)) /
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N := by
  let X := globalPooledColumnScale ell j
  let lengthScale := globalPooledLabelScale j
  let R := globalBinRadial ell (globalPooledRowScale K ell B F j) j
  let K' := globalLogRep j 8*Real.exp 1
  let Ct := globalTerminalConstant A₀ M
  let Q := C*(1+‖θ₁‖)^(2*J+2)*(1+‖θ₂‖)^(2*J+2)*(globalBinLossScale B j)^ε *
      (Ct*globalRayTripleConstant)*K*((ell*B^3)*F)
  have hB0 := zero_lt_one.trans_le hB
  have hF0 := zero_lt_one.trans_le hF
  have hX := globalPooledColumnScale_pos ell hell j
  have hL := globalPooledLabelScale_ge_one j
  have hR : 0 < R := globalBinRadial_pos ell _ hell (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
  have hK' : 1 ≤ K' := one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one j 8) (Real.one_le_exp (by norm_num))
  have hCt : 0 ≤ Ct := globalTerminalConstant_nonneg A₀ M
  have hrow : K' ≤ R*K := globalPooledRow_radial_bound K ell B F hK hell hB hF j hJ
  have hQ : 0 ≤ Q := by
    have hn : 0 ≤ globalBinLossScale B j := by
      have hh := (globalLogRep_pos j 4).le
      unfold globalBinLossScale;positivity
    unfold Q globalRayTripleConstant
    positivity
  have hterm (ray : SecondRayIndex) (q : Ideal O × Ideal O × Ideal O) :
      densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) V₁ V₂ X X (2*J)/(X*lengthScale) ≤ Ct*K'*(X*lengthScale) := by
    have h := SecondPassIntegration.childDensity_elementary_all_scales p hp hcop hg hc hinj pool
      (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (fun a => (secondRayMinus_norm_le Ψ ray a).trans (hΨ a))
      (fun a => (secondRayPlus_norm_le Ψ ray a).trans (hΨ a))
      (fixedTripleMask m q) (globalArithmeticTargets p s side q j) V₁ V₂ X lengthScale K' A₀ M J
      hX hL hK' hA₀ hM hV₁ hV₂ hVs₁ hVs₂ (globalArithmeticTargets_bounds p hp s side q j hk)
    apply h.trans
    apply mul_le_mul_of_nonneg_left
    · exact le_mul_of_one_le_right hX.le hL
    · exact mul_nonneg hCt (zero_le_one.trans hK')
  have hmass := globalDescentWeight_mass p hp C ε θ₁ θ₂ K ell B F (N+1) (2*J)
    hC hε hK hell hB0 hF0 side s j hk hb₁ hb₂
  calc
    _ ≤ ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q*(Ct*K'*(X*lengthScale)) := by
      apply Finset.sum_le_sum
      intro ray hray
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hterm ray q)
        (globalDescentWeight_nonneg C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q hC hK hell hB0 hF0)
    _ = Ct*K'*(∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q*(X*lengthScale)) := by
      simp only [Finset.mul_sum]
      congr 1
      funext ray
      congr 1
      funext q
      ring
    _ ≤ Ct*(R*K)*((C*(1+‖θ₁‖)^(2*J+2)*(1+‖θ₂‖)^(2*J+2)*(globalBinLossScale B j)^ε /
        (1+R)^(N+1))*globalRayTripleConstant*((ell*B^3)*F)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hrow hCt
      · exact hmass
      · apply Finset.sum_nonneg
        intro ray hray
        apply Finset.sum_nonneg
        intro q hq
        exact mul_nonneg (globalDescentWeight_nonneg C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q hC hK hell hB0 hF0)
          (mul_nonneg hX.le (zero_le_one.trans hL))
      · exact mul_nonneg hCt (mul_nonneg hR.le hK.le)
    _ = Q*(R/(1+R)^(N+1)) := by dsimp only [Q];ring
    _ ≤ Q*(1/(1+R)^N) := mul_le_mul_of_nonneg_left (radial_decay_step R hR.le N) hQ
    _ = _ := by dsimp only [Q,R,Ct];ring
end OAI.SecondPassArithmetic
