-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirst_diagonal_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:00:32.236202+00:00
-- url     : https://prove2.me/submissions/f413a8a1-e287-4dd5-9fa6-dfc89dd2d7c4

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SmoothTests
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DivisorTargets
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
import Theorems.Thm_OAI_SecondPassArithmetic_globalCubeActiveRoot_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalScaleIndex_bounds
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
open scoped BigOperators
open scoped BigOperators Classical
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (side : Bool) (b : GlobalFirstData ι) :
    globalFirstCoefficient p K ell B F side b*
        globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹ ≤
      (Real.exp 1)^3*ell*B^2*F*(1/primeProductNorm p b.common)*
        (1/primeProductNorm p b.firstCommon)*
        (1/‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
          (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖) := by
  let x := b.append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p side x
  let A := globalCubeActiveRoot p x
  have hbds := globalScaleIndex_bounds p hp side x (by exact one_ne_zero)
  have hc := (hbds 1).2
  have ha := (hbds 9).2
  change primeProductNorm p b.common≤globalLogRep j 1*Real.exp 1 at hc
  change A^2≤globalLogRep j 9*Real.exp 1 at ha
  have hcp := FirstPassCubeLabels.primeProductNorm_pos p hp b.common
  have htp := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon
  have hA := globalCubeActiveRoot_pos p hp x
  change 0<A at hA
  have h1 := globalLogRep_ge_one j 1
  have h4 := globalLogRep_ge_one j 4
  have h1p := globalLogRep_pos j 1
  have h4p := globalLogRep_pos j 4
  have h5p := globalLogRep_pos j 5
  have h9p := globalLogRep_pos j 9
  have h9s := Real.sqrt_pos.mpr h9p
  have he : 1≤Real.exp 1 := Real.one_le_exp (by norm_num)
  have has : A≤Real.sqrt (globalLogRep j 9)*Real.exp 1 := by
    apply (sq_le_sq₀ hA.le (mul_nonneg h9s.le (Real.exp_pos _).le)).mp
    rw [mul_pow,Real.sq_sqrt h9p.le]
    exact ha.trans (mul_le_mul_of_nonneg_left (by nlinarith : Real.exp 1≤(Real.exp 1)^2) h9p.le)
  have hcA : primeProductNorm p b.common*A ≤
      (Real.exp 1)^2*((globalLogRep j 1)^2*globalLogRep j 4*Real.sqrt (globalLogRep j 9)) := by
    calc
      _ ≤ (globalLogRep j 1*Real.exp 1)*(Real.sqrt (globalLogRep j 9)*Real.exp 1) :=
        mul_le_mul hc has hA.le (by positivity)
      _ = (Real.exp 1)^2*(globalLogRep j 1*1*1*Real.sqrt (globalLogRep j 9)) := by ring
      _ ≤ (Real.exp 1)^2*(globalLogRep j 1*globalLogRep j 1*globalLogRep j 4*Real.sqrt (globalLogRep j 9)) := by gcongr
      _ = _ := by ring
  have hr : 1/((globalLogRep j 1)^2*globalLogRep j 4*Real.sqrt (globalLogRep j 9))≤
      (Real.exp 1)^2/(primeProductNorm p b.common*A) := by
    apply (div_le_div_iff₀ (by positivity) (mul_pos hcp hA)).mpr
    simpa only [one_mul] using hcA
  change (K/(globalLogRep j 5*ell*B^2*F*Real.sqrt (globalLogRep j 9)))*
      (Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4))*
      (primeProductNorm p b.firstCommon)⁻¹≤_
  calc
    _ = (Real.exp 1*ell*B^2*F)*(1/((globalLogRep j 1)^2*globalLogRep j 4*Real.sqrt (globalLogRep j 9)))*
        (primeProductNorm p b.firstCommon)⁻¹ := by field_simp
    _ ≤ (Real.exp 1*ell*B^2*F)*((Real.exp 1)^2/(primeProductNorm p b.common*A))*
        (primeProductNorm p b.firstCommon)⁻¹ := by gcongr
    _ = _ := by change _ = (Real.exp 1)^3*ell*B^2*F*(1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*(1/A); ring
end OAI.SecondPassArithmetic
