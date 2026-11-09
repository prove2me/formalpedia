-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalPooled_log_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:04:17.220984+00:00
-- url     : https://prove2.me/submissions/4b865773-54b3-4a74-98ae-b68d28c5b90e

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_QuotientTopology
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalScaleVector_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_globalScaleIndex_error
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
import Theorems.Thm_OAI_SecondPassArithmetic_primeSubsetGenerator_norm_eq_productNorm
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
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    let j := globalScaleIndex p side x
    let d := expansionSupportData x.common x.firstDivisor x.source
    |secondSectorZ p (globalActualResidualScale p ell side x) (globalPooledColumnScale ell j) d| ≤ 6 ∧
    |secondSectorUd p (globalLogRep j 5) d| ≤ 6 ∧
    |secondSectorUe p (globalLogRep j 6) d| ≤ 6 ∧
    |secondSectorUv p (globalLogRep j 7) d| ≤ 6 ∧
    |secondSectorKap p (globalLogRep j 8) d| ≤ 6 := by
  let j := globalScaleIndex p side x
  let I : Finset (Fin 10) := {0,1,2,3,6,7}
  have hpos (i : Fin 10) : 0 < globalScaleVector p side x i :=
    zero_lt_one.trans_le (globalScaleVector_ge_one p hp side x hk i)
  have herr (i : Fin 10) := globalScaleIndex_error p hp side x hk i
  have hn (i : Fin 10) : globalScaleVector p side x i/globalLogRep j i ≠ 0 :=
    div_ne_zero (hpos i).ne' (globalLogRep_pos j i).ne'
  have hprod : primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
      globalActualResidualScale p ell side x =
      ∏ i∈I,globalScaleVector p side x i/globalLogRep j i := by
    have h (i : Fin 10) := (globalLogRep_pos j i).ne'
    have hA := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
    have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
    have ht := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).ne'
    have he := (FirstPassCubeLabels.primeProductNorm_pos p hp x.source.divisor).ne'
    have hr := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).ne'
    have prodI (f : Fin 10 → ℝ) : (∏ i ∈ I, f i) =
        f 0 * (f 1 * (f 2 * (f 3 * (f 6 * f 7)))) := by
      change (∏ i ∈ ({0,1,2,3,6,7} : Finset (Fin 10)), f i) = _
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
    rw [prodI]
    change _ = (primeProductNorm p (x.cube.sideDivisor side) / globalLogRep j 0) *
      ((primeProductNorm p x.common / globalLogRep j 1) *
      ((primeProductNorm p x.firstCommon / globalLogRep j 2) *
      ((primeProductNorm p (x.source.sourceCommon\x.source.divisor) / globalLogRep j 3) *
      ((primeProductNorm p x.source.divisor / globalLogRep j 6) *
      (primeProductNorm p x.source.overlap / globalLogRep j 7)))))
    norm_num [globalScaleVector,globalPooledColumnScale,globalActualResidualScale,globalFirstColumnScale]
    field_simp [h]
    <;> ring

  have hlog : 0 ≤ Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
      globalActualResidualScale p ell side x) ∧
      Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
        globalActualResidualScale p ell side x) ≤ 6 := by
    rw [hprod,Real.log_prod (fun i hi => hn i)]
    constructor
    · exact Finset.sum_nonneg (fun i hi => (herr i).1)
    · calc
        _ ≤ ∑ i∈I,(1 : ℝ) := Finset.sum_le_sum (fun i hi => (herr i).2)
        _ = 6 := by rw [Finset.sum_const, show I.card = 6 by decide]; norm_num
  have hsmall (i : Fin 10) : |Real.log (globalScaleVector p side x i/globalLogRep j i)| ≤ 6 := by
    rw [abs_of_nonneg (herr i).1]
    exact (herr i).2.trans (by norm_num)
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  · change |Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
      globalActualResidualScale p ell side x)| ≤ 6
    rw [abs_of_nonneg hlog.1]
    exact hlog.2
  · change |Real.log (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)‖^2 / globalLogRep j 5)| ≤ 6
    rw [primeSubsetGenerator_norm_eq_productNorm]
    exact hsmall 5
  · change |Real.log (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.source.divisor)‖^2 / globalLogRep j 6)| ≤ 6
    rw [primeSubsetGenerator_norm_eq_productNorm]
    exact hsmall 6
  · exact hsmall 7
  · exact hsmall 8
end OAI.SecondPassArithmetic
