-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.dualPrincipalIdeal_truncated_all_conductors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:19:18.881264+00:00
-- url     : https://prove2.me/submissions/69758417-38c3-4a75-ac05-412c1d08a621

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrincipalMajorants
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_RetainedDualBounds
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealGenerator_norm_sq
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealZeroMask_mul
import Theorems.Thm_OAI_CanonicalQuadraticSieve_singleton_rowCoprimeMask_eq_idealZeroMask
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealGenerator_ne_zero
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_actual_eisenstein_summable_norm
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
import Theorems.Thm_OAI_QuadraticUnitInvariance_rowCoprimeMask_norm_le_one
import Theorems.Thm_OAI_QuadraticUnitInvariance_rowCoprimeMask_unit_mul
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_OAI_UnrestrictedIdealReindex_tsum_unit_invariant_of_zero
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
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
open OAI.CanonicalQuadraticSieve
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
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson UnrestrictedIdealReindex GaussGeneratorTransport
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (V : 𝓢(ℝ,ℂ)) (X Y Z lengthScale : ℝ) (hX : 0<X) :
    dualPrincipalIdeal I J V X = (6:ℂ)⁻¹ *
      (principalTruncation (fun P : primePool {I*J} => P.val) Finset.univ V X Z +
       middleTruncation (fun P : primePool {I*J} => P.val) Finset.univ V X Y Z lengthScale +
       truncationError (fun P : primePool {I*J} => P.val) Finset.univ V X Y Z lengthScale) := by
  let P := fun P : primePool {I*J} => P.val
  let f : O → ℂ := fun z => rowCoprimeMask P Finset.univ z *
    (if z=0 then 0 else V (‖eisEmbedding z‖^2/X))
  have hV : Summable (fun z : O => ‖V (‖eisEmbedding z‖^2/X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest V X hX)
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hV
    intro z
    dsimp only [f]
    by_cases hz : z=0
    · simp only [hz,ite_true,mul_zero,norm_zero]
      exact norm_nonneg _
    · rw [if_neg hz,norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (QuadraticUnitInvariance.rowCoprimeMask_norm_le_one P Finset.univ z)
  have h0 : f 0=0 := by simp only [f,ite_true,mul_zero]
  have hu (u : Oˣ) (z : O) : f (u.val*z)=f z := by
    dsimp only [f]
    rw [QuadraticUnitInvariance.rowCoprimeMask_unit_mul,norm_eisEmbedding_unit_mul]
    simp only [mul_eq_zero,u.ne_zero,false_or]
  have he := tsum_unit_invariant_of_zero f hf h0 hu
  have hm (z : O) : rowCoprimeMask P Finset.univ z=idealZeroMask I z*idealZeroMask J z := by
    rw [singleton_rowCoprimeMask_eq_idealZeroMask,idealZeroMask_mul I J hI.1 hJ.1]
  have hd : (∑' A : NonzeroIdeal, f (idealGenerator A.val))=dualPrincipalIdeal I J V X := by
    unfold dualPrincipalIdeal
    apply tsum_congr
    intro A
    simp only [f,hm,if_neg (idealGenerator_ne_zero A.val A.property),idealGenerator_norm_sq]
  rw [hd] at he
  have hs : principalTruncation P Finset.univ V X Z + middleTruncation P Finset.univ V X Y Z lengthScale +
      truncationError P Finset.univ V X Y Z lengthScale = ∑' z : O, f z := by
    unfold truncationError
    dsimp only [f]
    ring
  change dualPrincipalIdeal I J V X=(6:ℂ)⁻¹ *
    (principalTruncation P Finset.univ V X Z + middleTruncation P Finset.univ V X Y Z lengthScale +
      truncationError P Finset.univ V X Y Z lengthScale)
  rw [hs,he]
  ring
end OAI.CanonicalQuadraticSieve
