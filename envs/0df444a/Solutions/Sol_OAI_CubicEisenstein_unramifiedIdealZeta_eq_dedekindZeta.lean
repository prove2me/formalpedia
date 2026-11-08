-- Prove2me | solution 1 for OAI.CubicEisenstein.unramifiedIdealZeta_eq_dedekindZeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:14:10.347196+00:00
-- url     : https://prove2.me/submissions/92dcd439-7402-4e43-aa08-98d93083f54c

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConstantDirichletSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DyadicColumns
import Theorems.Thm_OAI_CubicEisenstein_fullIdealWeight_summable_norm
import Theorems.Thm_OAI_CubicEisenstein_fullIdealZeta_eq_dedekindZeta
import Theorems.Thm_OAI_CubicEisenstein_fullIdealWeight_lambdaFactor
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_unramifiedNormWeight_of_bad
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
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
namespace OAI.CubicEisenstein
theorem _root_.solution (s : ℂ) (hs : 1<s.re) :
    unramifiedIdealZeta s=(1-(3:ℂ)^(-s))*NumberField.dedekindZeta ActualEisensteinCubic.K s := by
  have hnorm : ‖(3:ℂ)^(-s)‖<1 := by
    change ‖((3:ℝ):ℂ)^(-s)‖<1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    simp only [Complex.neg_re]
    linarith
  have hne : 1-(3:ℂ)^(-s) ≠ 0 := by
    intro h
    have hz : (3:ℂ)^(-s)=1 := (sub_eq_zero.mp h).symm
    rw [hz,norm_one] at hnorm
    exact lt_irrefl 1 hnorm
  have hsub : Summable (fun I : NonzeroIdeal => fullIdealWeight s I.1) :=
    (fullIdealWeight_summable_norm s hs).of_norm.subtype _
  have hp := lambdaFactorEquiv.summable_iff.mpr hsub
  change Summable (fun p : ℕ × GoodIdeal => fullIdealWeight s (lambdaFactorMap p).1) at hp
  have hfull : fullIdealZeta s=(1-(3:ℂ)^(-s))⁻¹*unramifiedIdealZeta s := by
    calc
      _ = ∑' I : NonzeroIdeal,fullIdealWeight s I.1 := by
        symm
        apply tsum_subtype_eq_of_support_subset
        intro I hI
        change I ≠ 0
        intro hz
        exact hI (by simp [fullIdealWeight,hz])
      _ = ∑' p : ℕ × GoodIdeal,fullIdealWeight s (lambdaFactorMap p).1 :=
        (lambdaFactorEquiv.tsum_eq _).symm
      _ = ∑' n : ℕ,∑' I : GoodIdeal,((3:ℂ)^(-s))^n*unramifiedNormWeight s I.1 := by
        rw [hp.tsum_prod]
        apply tsum_congr; intro n
        exact tsum_congr (fun I => fullIdealWeight_lambdaFactor s n I)
      _ = ∑' n : ℕ,((3:ℂ)^(-s))^n*unramifiedIdealZeta s := by
        apply tsum_congr; intro n
        rw [tsum_mul_left]
        apply congrArg (fun z : ℂ => ((3:ℂ)^(-s))^n*z)
        apply tsum_subtype_eq_of_support_subset (f := unramifiedNormWeight s)
          (s := {I : Ideal O | primaryGenerator I ≠ 0})
        intro I hI
        change primaryGenerator I ≠ 0
        intro hz
        exact hI (unramifiedNormWeight_of_bad s I hz)
      _ = _ := by rw [tsum_mul_right,tsum_geometric_of_norm_lt_one hnorm]
  rw [← fullIdealZeta_eq_dedekindZeta s hs,hfull,← mul_assoc,mul_inv_cancel₀ hne,one_mul]
end OAI.CubicEisenstein
