-- Prove2me | solution 1 for OAI.CubicEisenstein.actual_eisenstein_cylinder_green
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T15:47:21.958965+00:00
-- url     : https://prove2.me/submissions/f11276b0-1499-4d4b-a62e-8cad5e91296a

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LogarithmicTargets
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspIntegration
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_cuspBoxIntegral_add
import Theorems.Thm_OAI_CubicEisenstein_cuspBoxIntegral_const_mul
import Theorems.Thm_OAI_CubicEisenstein_extendAboveHeight_continuous
import Theorems.Thm_OAI_CubicEisenstein_extendAboveHeight_eq
import Theorems.Thm_OAI_CubicEisenstein_greenFields_continuousAt
import Theorems.Thm_OAI_CubicEisenstein_actual_green_fields_density
import Theorems.Thm_OAI_CubicEisenstein_cuspBoxIntegral_congr
import Theorems.Thm_OAI_CubicEisenstein_cuspBox_green_axis_zero
import Theorems.Thm_OAI_CubicEisenstein_cuspBox_green_axis_one
import Theorems.Thm_OAI_CubicEisenstein_cuspBox_green_vertical
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
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
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
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


attribute [local simp] OAI.CubicEisenstein.spatialTriple_zero
attribute [local simp] OAI.CubicEisenstein.spatialTriple_one
attribute [local simp] OAI.CubicEisenstein.spatialTriple_two

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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology
namespace OAI.CubicEisenstein
theorem _root_.solution (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    (s*(s-2)-star (t*(t-2)))*cuspBoxIntegral a b (eisensteinHermitianDensity s t)=
      ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        greenBoundaryFlux s t (spatialTriple x y b)-greenBoundaryFlux s t (spatialTriple x y a) := by
  let f₀ := extendAboveHeight a (greenAxisDensity s t 0)
  let f₁ := extendAboveHeight a (greenAxisDensity s t 1)
  let f₂ := extendAboveHeight a (greenVerticalDensity s t)
  have h₀ : Continuous f₀ := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).1 0)
  have h₁ : Continuous f₁ := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).1 1)
  have h₂ : Continuous f₂ := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).2.1)
  have hD : cuspBoxIntegral a b (fun p => f₀ p+f₁ p+f₂ p)=
      (s*(s-2)-star (t*(t-2)))*cuspBoxIntegral a b (eisensteinHermitianDensity s t) := by
    rw [← cuspBoxIntegral_const_mul]
    apply cuspBoxIntegral_congr
    intro p hp
    change extendAboveHeight a (greenAxisDensity s t 0) p+
      extendAboveHeight a (greenAxisDensity s t 1) p+
      extendAboveHeight a (greenVerticalDensity s t) p=_
    rw [extendAboveHeight_eq _ _ _ hp.1,extendAboveHeight_eq _ _ _ hp.1,extendAboveHeight_eq _ _ _ hp.1,
      actual_green_fields_density s t hs ht p (lt_of_lt_of_le ha hp.1)]
    unfold eisensteinHermitianDensity
    ring
  rw [← hD,cuspBoxIntegral_add (fun p => f₀ p+f₁ p) f₂ (h₀.add h₁) h₂,
    cuspBoxIntegral_add f₀ f₁ h₀ h₁]
  rw [cuspBox_green_axis_zero s t hs ht a b ha hab,cuspBox_green_axis_one s t hs ht a b ha hab,
    cuspBox_green_vertical s t hs ht a b ha hab]
  simp only [zero_add]
end OAI.CubicEisenstein
