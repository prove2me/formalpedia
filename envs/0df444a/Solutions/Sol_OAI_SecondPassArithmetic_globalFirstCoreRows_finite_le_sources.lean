-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstCoreRows_finite_le_sources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:26:32.182194+00:00
-- url     : https://prove2.me/submissions/dba11b8a-bdb9-49c5-8047-0686449a1767

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstTruncatedSource_split
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstCoreRows_smoothed
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
import Theorems.Thm_OAI_SecondPassArithmetic_firstCoreInputRow_finite_le_corrected_source
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


attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.append_first
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.first_append
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.source_append

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
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
    (hw : ∀ b∈s,0 ≤ w b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ)
    (Y : GlobalFirstData ι → ℝ) (hY : ∀ b∈s,0 < Y b)
    (T : GlobalFirstData ι → Finset O)
    (hT : ∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y b)
    (hT0 : ∀ b∈s,∀ z∈T b,z ≠ 0) :
    (∑ b∈s,w b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
      globalFirstCoreCorrection p g V ell side t b)) ≤
      ‖globalFirstTruncatedSource p hp hg hinj pool s (fun b => w b)
        (fun b G E => (cutoff b G E).erase 0) (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ +
      ‖globalFirstSourceZero p hg pool s (fun b => w b) cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ +
      ‖globalFirstSourceTail p hp hg hinj pool s (fun b => w b) cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ := by
  have henergy : (∑ b∈s,w b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
      globalFirstCoreCorrection p g V ell side t b)) ≤
      (∑ b∈s,(w b : ℂ)*∑' z : O,rowMajorant (‖eisEmbedding z‖^2/Y b)*
        (‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2 : ℝ)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_le_sum
    intro b hb
    have hh := firstCoreInputRow_finite_le_corrected_source p hg
      (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
      side χ Ψ m (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
      V (columnLog p (globalFirstBlockColumnScale p ell side b))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r t (T b) (Y b) (hY b hb) (hT b hb) (hT0 b hb)
    have hh' := mul_le_mul_of_nonneg_left (le_sub_iff_add_le.mp hh) (hw b hb)
    simpa only [globalFirstCoreRow,globalFirstCoreCorrection,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using hh'
  rw [globalFirstCoreRows_smoothed p hp hg hinj hc pool s (fun b => w b) cutoff Ψ m g V rowMajorant ell hell side χ r t Y hY,
    globalFirstTruncatedSource_split] at henergy
  exact henergy.trans ((Complex.re_le_norm _).trans ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)))
end OAI.SecondPassArithmetic
