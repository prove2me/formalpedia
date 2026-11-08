-- Prove2me | solution 1 for OAI.CubicEisenstein.scatteringCoefficient_zero_oneSidedResidue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:19:18.465186+00:00
-- url     : https://prove2.me/submissions/7c5ff539-0413-401d-b1be-1a860ce60ed5

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConstantDirichletSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DyadicColumns
import Theorems.Thm_OAI_CubicEisenstein_unramifiedIdealZeta_differentiableAt
import Theorems.Thm_OAI_CubicEisenstein_unramifiedIdealZeta_oneSidedResidue
import Theorems.Thm_OAI_CubicEisenstein_tendsto_three_mul_sub_three_four_thirds
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_scatteringCoefficient_zero_zeta
import Theorems.Thm_OAI_CubicEisenstein_unramifiedIdealZeta_ne_zero
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
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
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
open scoped BigOperators Classical
open OAI.CubicEisenstein
open Filter
open scoped BigOperators Classical Topology
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
namespace OAI.CubicEisenstein
theorem _root_.solution :
    Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*scatteringCoefficient (x:ℂ) 0)
      (𝓝[>] ((4:ℝ)/3)) (𝓝 constantArithmeticResidue) := by
  have hn0 := unramifiedIdealZeta_oneSidedResidue.comp tendsto_three_mul_sub_three_four_thirds
  have hn : Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*unramifiedIdealZeta (3*(x:ℂ)-3))
      (𝓝[>] ((4:ℝ)/3)) (𝓝 (unramifiedZetaResidue/3)) := by
    convert hn0.div_const (3:ℂ) using 1
    ext x
    dsimp only [Function.comp_def]
    push_cast
    ring
  have harg : Tendsto (fun x : ℝ => 3*(x:ℂ)-2) (𝓝[>] ((4:ℝ)/3)) (𝓝 (2:ℂ)) := by
    apply (((Complex.continuous_ofReal.const_mul 3).sub continuous_const).tendsto' _ _ ?_).mono_left
      nhdsWithin_le_nhds
    norm_num
  have hz := (unramifiedIdealZeta_differentiableAt 2 (by norm_num)).continuousAt.tendsto.comp harg
  have hdncont : Continuous (fun x : ℝ => (3:ℂ)^(3*(x:ℂ)-3)-1) :=
    (((Complex.continuous_ofReal.const_mul 3).sub continuous_const).const_cpow
      (Or.inl (by norm_num))).sub continuous_const
  have hdn : Tendsto (fun x : ℝ => (3:ℂ)^(3*(x:ℂ)-3)-1)
      (𝓝[>] ((4:ℝ)/3)) (𝓝 (2:ℂ)) := by
    apply (hdncont.tendsto' _ _ ?_).mono_left nhdsWithin_le_nhds
    norm_num
  have hp := ((hdn.inv₀ (by norm_num)).const_mul
    (2/((9*Real.sqrt 3/2:ℝ):ℂ))).mul
      (hn.div hz (unramifiedIdealZeta_ne_zero 2 (by norm_num)))
  have hlimit : (2/((9*Real.sqrt 3/2:ℝ):ℂ))*(2:ℂ)⁻¹*
      ((unramifiedZetaResidue/3)/unramifiedIdealZeta 2)=constantArithmeticResidue := by
    unfold constantArithmeticResidue
    ring
  rw [hlimit] at hp
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : (4:ℝ)/3<(x:ℂ).re := by simpa only [Set.mem_Ioi,Complex.ofReal_re] using hx
  rw [scatteringCoefficient_zero_zeta (x:ℂ) hx']
  dsimp only [Pi.div_apply,Function.comp_def]
  ring
end OAI.CubicEisenstein
