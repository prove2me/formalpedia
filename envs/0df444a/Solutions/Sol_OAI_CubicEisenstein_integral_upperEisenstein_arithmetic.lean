-- Prove2me | solution 1 for OAI.CubicEisenstein.integral_upperEisenstein_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:02:35.583204+00:00
-- url     : https://prove2.me/submissions/4fcf0cc4-5c1f-48dd-8cd1-c7a5670ad817

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_HyperbolicSpace
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowMajorants
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FourierCoefficients
import Theorems.Thm_OAI_CubicEisenstein_hasSum_primitiveRowIntegrals
import Theorems.Thm_OAI_CubicEisenstein_denominator_integral_formula
import Theorems.Thm_OAI_CubicEisenstein_zero_lower_integral
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
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
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
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
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply



set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open MeasureTheory Set Filter
open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
namespace OAI.CubicEisenstein
theorem _root_.solution (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) (h : O) :
    (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      (v:ℂ)^s*(if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0)+
        ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*arithmeticDirichletSeries s h := by
  let c0 : LevelLower := ⟨0,dvd_zero _⟩
  let F (c : LevelLower) := ∑' d : AdmissibleDenominator c.1,
    primitiveRowIntegral v s (cuspFrequency h) c.1 d.1
  have hsum := hasSum_primitiveRowIntegrals v hv s (cuspFrequency h) hs
  have hF : Summable F := hsum.summable.sigma
  have hzero : F c0=(v:ℂ)^s*(if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0) :=
    zero_lower_integral v s h
  calc
    _ = ∑' c : LevelLower,F c := hsum.tsum_eq.symm.trans hsum.summable.tsum_sigma
    _ = F c0+∑' c : LevelLower,if c=c0 then 0 else F c := hF.tsum_eq_add_tsum_ite c0
    _ = _ := by
      rw [hzero]
      congr 1
      rw [arithmeticDirichletSeries,← tsum_mul_left]
      apply tsum_congr
      intro c
      by_cases hc : c.1=0
      · have heq : c=c0 := Subtype.ext hc
        simp only [heq,ite_true,arithmeticDirichletTerm,c0,mul_zero]
      · have heq : c ≠ c0 := fun heq => hc (congrArg Subtype.val heq)
        rw [if_neg heq]
        change (∑' d : AdmissibleDenominator c.1,
          primitiveRowIntegral v s (cuspFrequency h) c.1 d.1)=_
        rw [denominator_integral_formula v hv s hs h c hc]
        simp only [arithmeticDirichletTerm,if_neg hc]
        ring
end OAI.CubicEisenstein
