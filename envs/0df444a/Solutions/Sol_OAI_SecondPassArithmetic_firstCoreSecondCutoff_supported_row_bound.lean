-- Prove2me | solution 1 for OAI.SecondPassArithmetic.firstCoreSecondCutoff_supported_row_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T15:16:45.095306+00:00
-- url     : https://prove2.me/submissions/c6ffca40-5e9c-4c5b-aa32-067514011f9a

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_GreenIdentity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LogarithmicTargets
import Theorems.Thm_OAI_SecondPassArithmetic_supported_cutoff_denominator
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
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_mono
import Theorems.Thm_OAI_SecondPassArithmetic_primeSubsetGenerator_norm_eq_productNorm
import Theorems.Thm_OAI_SecondPassArithmetic_secondFrequencyCutoff_norm_sq_le
import Theorems.Thm_OAI_SecondPassArithmetic_secondSourceSupport_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportedSector_mem
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
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (D A F R : Finset ι) (X Y M Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 ≤ Z)
    (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F (firstCoreSecondCutoff p A X Y M Z) R
      (X/primeProductNorm p A) M) :
    ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤
      firstCoreSecondRowBound p D A X Y M Z := by
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F
    (firstCoreSecondCutoff p A X Y M Z) R (X/primeProductNorm p A) M x hx
  let U := (X/primeProductNorm p A)*Real.exp M
  have hU : 0 < U := mul_pos (div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp A)) (Real.exp_pos _)
  have hNE := FirstPassCubeLabels.primeProductNorm_pos p hp x.divisor
  have hNG := FirstPassCubeLabels.primeProductNorm_pos p hp x.sourceCommon
  have hEupper : primeProductNorm p x.divisor ≤ U :=
    (secondSourceSupport_bounds p hp _ M x hs hE).2.1
  have hden : primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2 ≤ U^2 := by
    rw [show ((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M =
      U/primeProductNorm p x.sourceCommon by dsimp [U]; ring]
    exact supported_cutoff_denominator _ _ _ (primeProductNorm_mono p hp hE) (primeProductNorm_ge_one p hp _)
  have hdenpos : 0 < primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2 := by
    exact mul_pos hNE (sq_pos_of_pos (mul_pos (div_pos (div_pos hX
      (FirstPassCubeLabels.primeProductNorm_pos p hp A)) hNG) (Real.exp_pos _)))
  have hratio : Z / (Y / (primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2)) ≤ Z*U^2/Y := by
    rw [div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hden hZ) hY.le
  have hceil : (⌈Z / (Y / (primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2))⌉₊ : ℝ) ≤
      (⌈Z*U^2/Y⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_mono hratio
  have hkbound := secondFrequencyCutoff_norm_sq_le _ Z x.frequency hk
  simp only [ primeSubsetGenerator_norm_eq_productNorm] at hkbound
  have hkbound' : ‖eisEmbedding x.frequency‖^2 ≤ 3*((⌈Z*U^2/Y⌉₊ : ℝ)+1)^2 := by
    apply hkbound.trans
    gcongr
  have hrow : ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 =
      primeProductNorm p D * primeProductNorm p x.divisor * ‖eisEmbedding x.frequency‖^2 := by
    simp only [actualSecondRow, map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_eq_productNorm]
  rw [hrow]
  calc
    _ ≤ (primeProductNorm p D * U) * (3*((⌈Z*U^2/Y⌉₊ : ℝ)+1)^2) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hEupper (FirstPassCubeLabels.primeProductNorm_pos p hp D).le)
        hkbound' (sq_nonneg _) (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp D) hU).le
    _ = firstCoreSecondRowBound p D A X Y M Z := by unfold firstCoreSecondRowBound; dsimp [U]; ring
end OAI.SecondPassArithmetic
