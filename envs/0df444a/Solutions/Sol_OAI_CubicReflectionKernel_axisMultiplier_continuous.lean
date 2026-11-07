-- Prove2me | solution 1 for OAI.CubicReflectionKernel.axisMultiplier_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:33:12.762401+00:00
-- url     : https://prove2.me/submissions/51897467-bdf5-4a8f-9037-03caa30063ba

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoefficientCancellation
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_CubicReflectionKernel_Gamma_vertical_ne_zero
import Theorems.Thm_OAI_CubicReflectionKernel_Gamma_vertical_continuous
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
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
open scoped BigOperators Classical SchwartzMap
open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory
open OAI.CubicReflectionKernel
namespace OAI.CubicReflectionKernel
theorem _root_.solution : Continuous axisMultiplier := by
  have h1 := (Gamma_vertical_continuous (7 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => 2 * Real.pi * u) by fun_prop)
  have h2 := (Gamma_vertical_continuous (5 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => 2 * Real.pi * u) by fun_prop)
  have h3 := (Gamma_vertical_continuous (7 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => -(2 * Real.pi * u)) by fun_prop)
  have h4 := (Gamma_vertical_continuous (5 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => -(2 * Real.pi * u)) by fun_prop)
  have hd := h3.mul h4
  have hne (u : ℝ) :
      Complex.Gamma ((7 / 6 : ℝ) + (-(2 * Real.pi * u) : ℝ) * Complex.I) *
      Complex.Gamma ((5 / 6 : ℝ) + (-(2 * Real.pi * u) : ℝ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Gamma_vertical_ne_zero _ _ (by norm_num)) (Gamma_vertical_ne_zero _ _ (by norm_num))
  convert (h1.mul h2).div hd hne using 1
  ext u
  simp only [axisMultiplier, gammaMultiplier, Function.comp_def, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg,
    Pi.div_apply, Pi.mul_apply]
end OAI.CubicReflectionKernel
