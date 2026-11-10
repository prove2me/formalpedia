-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_subbin_cost_radial_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T23:31:36.98532+00:00
-- url     : https://prove2.me/submissions/d9ea4877-7e97-4d88-a03d-3d4f4e3f5f41

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_DiagonalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HighRadialBounds
import Theorems.Thm_OAI_InitialMeanSquare_initialElementaryConstant_nonneg
import Theorems.Thm_OAI_InitialMeanSquare_initial_subbin_cost_elementary
import Theorems.Thm_OAI_InitialMeanSquare_initial_radial_absorbs_rows
import Theorems.Thm_OAI_InitialMeanSquare_initialHighRadialConstant_nonneg
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
import Theorems.Thm_OAI_FirstPassCubeLabels_firstLogDensity_nonneg
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
import Theorems.Thm_OAI_SecondPassArithmetic_normLogScale_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_normLogScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_ge_one
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
open OAI.InitialMeanSquare
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
open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)
variable {ι : Type*} [DecidableEq ι] (p : ι → OAI.InitialMeanSquare.O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (OAI.InitialMeanSquare.O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hc hinj
namespace OAI.InitialMeanSquare
theorem _root_.solution (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hε : ε ≤ 1)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : Frequency → ℝ) (J N : ℕ) (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialRestrictedBinCost p hp hcop hg F R Ψ m ray s Z H ε j V₁ V₂ B ≤
      initialHighRadialConstant A Vmax Cs*Z^4/primeProductNorm p R*
        ‖secondRayCoefficient ray‖/(1+initialRadial Z H (primeProductNorm p R) j)^N := by
  have hH0 := zero_lt_one.trans_le hH
  have hb := initial_subbin_cost_elementary p hp hcop hg hc hinj F R Ψ hΨ m ray K Z H M
    ε A Vmax Cs hZ hH0 hA hVmax hCs j s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J (N+2) hB hdec
  have hR1 := primeProductNorm_ge_one p hp R
  have hR0 := zero_lt_one.trans_le hR1
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hrow : 1 ≤ secondLogK j*Real.exp 2 :=
    one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  have hrowpow : (secondLogK j*Real.exp 2)^ε ≤ secondLogK j*Real.exp 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hrow hε
  have hcc := initialElementaryConstant_nonneg A Vmax
  have hi : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t := integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hfixed := initialHighRadialConstant_nonneg A Vmax Cs hCs
  have hpref : 0 ≤ ((H/primeProductNorm p R)*Real.exp 4*
      (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
      (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖ := by positivity
  have hden : 0 ≤ (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2) := by positivity
  apply hb.trans
  calc
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*
        (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
        (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖*
        (secondLogK j*Real.exp 2)/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrowpow hpref) hden
    _ = (initialHighRadialConstant A Vmax Cs/primeProductNorm p R*‖secondRayCoefficient ray‖)*
        (H*(secondLogK j)^2/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)) := by
      unfold initialHighRadialConstant
      have he : Real.exp 4*(Real.exp 2)^2=Real.exp 8 := by
        rw [pow_two,←Real.exp_add,←Real.exp_add]; norm_num
      rw [←he]
      ring
    _ ≤ (initialHighRadialConstant A Vmax Cs/primeProductNorm p R*‖secondRayCoefficient ray‖)*
        (Z^4/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N) :=
      mul_le_mul_of_nonneg_left (initial_radial_absorbs_rows Z H (primeProductNorm p R)
        (secondLogK j) N hZ hH hR1 hk.le) (by positivity)
    _ = _ := by unfold initialRadial; ring
end OAI.InitialMeanSquare
